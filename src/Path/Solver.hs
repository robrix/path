{-# LANGUAGE FlexibleContexts, LambdaCase, TypeApplications, TypeOperators #-}
module Path.Solver where

import           Control.Effect
import           Control.Effect.Error
import           Control.Effect.Fresh
import           Control.Effect.Reader hiding (Local)
import           Control.Effect.State
import           Control.Effect.Writer
import           Control.Monad (when)
import           Data.Foldable (fold, foldl')
import           Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Map as Map
import           Data.Maybe (catMaybes, fromMaybe)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import           Path.Constraint
import           Path.Error
import           Path.Eval
import           Path.Name
import           Path.Plicity
import           Path.Scope
import           Path.Stack
import           Path.Value hiding (Scope (..))
import           Prelude hiding (pi)

simplify :: ( Carrier sig m
            , Effect sig
            , Member (Error ElabError) sig
            , Member Fresh sig
            , Member (Reader Gensym) sig
            , Member (Reader Scope) sig
            )
         => Caused (Equation (Value MName) ::: Type MName)
         -> m (Set.Set (Caused (Equation (Value MName) ::: Type MName)))
simplify = execWriter . go
  where go = \case
          (tm1 :===: tm2) ::: _ :@ _ | tm1 == tm2 -> pure ()
          q@((Pi p1 u1 t1 b1 :===: Pi p2 u2 t2 b2) ::: Type) :@ cause
            | p1 == p2, u1 == u2 -> do
              (_, n) <- freshName
              go ((t1               :===: t2              ) ::: Type :@ Via q cause)
              go ((instantiate n b1 :===: instantiate n b2) ::: Type :@ Via q cause)
          q@((Pi Im _ _ b1 :===: t2) ::: Type) :@ cause -> do
            n <- exists
            go ((instantiate n b1 :===: t2) ::: Type :@ Via q cause)
          q@((t1 :===: Pi Im _ _ b2) ::: Type) :@ cause -> do
            n <- exists
            go ((t1 :===: instantiate n b2) ::: Type :@ Via q cause)
          q@((Lam b1 :===: Lam b2) ::: Pi _ _ t b) :@ cause -> do
            (_, n) <- freshName
            go ((instantiate n b1 :===: instantiate n b2) ::: instantiate t b :@ Via q cause)
          q@((f1@(Qual (_ :.: _)) :$ sp1 :===: f2@(Qual (_ :.: _)) :$ sp2) ::: ty) :@ cause -> do
            t1 <- whnf (f1 :$ sp1)
            t2 <- whnf (f2 :$ sp2)
            go ((t1 :===: t2) ::: ty :@ Via q cause)
          q@((f1@(Qual (_ :.: _)) :$ sp1 :===: t2) ::: ty) :@ cause -> do
            t1 <- whnf (f1 :$ sp1)
            go ((t1 :===: t2) ::: ty :@ Via q cause)
          q@((t1 :===: f2@(Qual (_ :.: _)) :$ sp2) ::: ty) :@ cause -> do
            t2 <- whnf (f2 :$ sp2)
            go ((t1 :===: t2) ::: ty :@ Via q cause)
          q@((tm1 :===: Lam b2) ::: ty) :@ cause -> do
            (n, v) <- freshName
            go ((lam n (tm1 $$ v) :===: Lam b2) ::: ty :@ Via q cause)
          q@((Lam b1 :===: tm2) ::: ty) :@ cause -> do
            (n, v) <- freshName
            go ((Lam b1 :===: lam n (tm2 $$ v)) ::: ty :@ Via q cause)
          q@((t1 :===: t2) ::: _ :@ cause)
            | stuck t1                 -> tell (Set.singleton q)
            | stuck t2                 -> tell (Set.singleton q)
            | span :| _ <- spans cause -> throwError (ElabError span mempty (TypeMismatch (Set.singleton q)))
        freshName = ((,) <*> pure) . qlocal <$> gensym ""
        exists = pure . Meta <$> gensym "_meta_"

        stuck (Meta _ :$ _) = True
        stuck _             = False

solve :: ( Carrier sig m
         , Effect sig
         , Member (Error ElabError) sig
         , Member (Reader Gensym) sig
         , Member (Reader Scope) sig
         )
      => Set.Set (Caused (Equation (Value MName) ::: Type MName))
      -> m [Caused Solution]
solve cs
  = local (// "solve")
  . runFresh
  . fmap (map (uncurry toSolution) . Map.toList)
  . execState mempty
  . evalState (Seq.empty :: Seq.Seq (Caused (Equation (Value MName) ::: Type MName)))
  $ do
    stuck <- fmap fold . execState (mempty :: Map.Map Gensym (Set.Set (Caused (Equation (Value MName) ::: Type MName)))) $ do
      modify (flip (foldl' (Seq.|>)) cs)
      step
    case Set.minView stuck of
      Nothing     -> pure ()
      Just (c, _) -> throwMismatch stuck (cause c)
  where step = dequeue >>= \case
          Just q -> do
            _S <- get
            process _S q
            step
          Nothing -> pure ()

        process _S q@((t1 :===: t2) ::: _ :@ c)
          | Just s <- solutions _S (metaNames (fvs t1 <> fvs t2)) = simplify (apply s q) >>= modify . flip (foldl' (Seq.|>))
          | Just (m, sp) <- pattern t1 = solve (m := lams sp t2 :@ c)
          | Just (m, sp) <- pattern t2 = solve (m := lams sp t1 :@ c)
          | otherwise = enqueue q

        enqueue q = do
          let s = Set.singleton q
              mvars = metaNames (fvs q)
          when (Prelude.null mvars) (throwMismatch (Set.singleton q) (cause q))
          modify (Map.unionWith (<>) (foldl' (\ m i -> Map.insertWith (<>) i s m) mempty mvars))

        dequeue = gets Seq.viewl >>= \case
          Seq.EmptyL -> pure Nothing
          h Seq.:< q -> Just h <$ put q

        pattern (Meta m :$ sp) = (,) m <$> traverse free sp
        pattern _              = Nothing

        free (v :$ Nil) = Just v
        free _          = Nothing

        solve (m := v :@ c) = do
          modify (Map.insert m (v :@ c))
          cs <- gets (fromMaybe mempty . Map.lookup m)
          modify (flip (foldl' (Seq.|>)) (cs :: Set.Set (Caused (Equation (Value MName) ::: Type MName))))
          modify (Map.delete @Gensym @(Set.Set (Caused (Equation (Value MName) ::: Type MName))) m)

        solutions _S s
          | s:ss <- catMaybes (solution _S <$> Set.toList s) = Just (s:ss)
          | otherwise                                        = Nothing
        solution _S m = toSolution m <$> Map.lookup m _S

        toSolution m (v :@ c) = m := v :@ c

        throwMismatch qs c | span :| _ <- spans c = throwError (ElabError span mempty (TypeMismatch qs))
