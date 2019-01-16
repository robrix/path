{-# LANGUAGE FlexibleContexts, LambdaCase, TypeApplications #-}
module Path.Solver where

import           Control.Effect
import           Control.Effect.Error
import           Control.Effect.Fresh
import           Control.Effect.Reader hiding (Local)
import           Control.Effect.State
import           Control.Effect.Writer
import           Control.Monad ((>=>), unless, when)
import           Data.Foldable (fold, foldl', for_, toList)
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
import           Path.Usage
import           Path.Value hiding (Scope (..))
import           Prelude hiding (pi)

simplify :: ( Carrier sig m
            , Effect sig
            , Member (Error ElabError) sig
            , Member Fresh sig
            , Member (Reader Gensym) sig
            , Member (Reader Scope) sig
            , Monad m
            )
         => Caused (Equation Value)
         -> m (Set.Set (Caused (Equation Value)))
simplify = execWriter . go
  where go = \case
          tm1 :===: tm2 :@ _ | tm1 == tm2 -> pure ()
          Pi p1 u1 t1 b1 :===: Pi p2 u2 t2 b2 :@ cause
            | p1 == p2, u1 == u2 -> do
              (_, n) <- freshName t1
              go (t1               :===: t2               :@ cause)
              go (instantiate n b1 :===: instantiate n b2 :@ cause)
          Pi Im _ ty1 b1 :===: t2 :@ cause -> do
            n <- exists ty1
            go (instantiate n b1 :===: t2 :@ cause)
          t1 :===: Pi Im _ ty2 b2 :@ cause -> do
            n <- exists ty2
            go (t1 :===: instantiate n b2 :@ cause)
          Lam t1 b1 :===: Lam t2 b2 :@ cause -> do
            (_, n) <- freshName t1
            go (t1               :===: t2               :@ cause)
            go (instantiate n b1 :===: instantiate n b2 :@ cause)
          (f1 ::: tf1) :$ sp1 :===: (f2 ::: tf2) :$ sp2 :@ cause
            | f1 == f2, length sp1 == length sp2 -> do
              go (tf1 :===: tf2 :@ cause)
              for_ (zipWith (:===:) (toList sp1) (toList sp2)) (go . (:@ cause))
          f1@(Free (Q (_ :.: _)) ::: _) :$ sp1 :===: f2@(Free (Q (_ :.: _)) ::: _) :$ sp2 :@ cause -> do
            t1 <- whnf (f1 :$ sp1)
            t2 <- whnf (f2 :$ sp2)
            go (t1 :===: t2 :@ cause)
          f1@(Free (Q (_ :.: _)) ::: _) :$ sp1 :===: t2 :@ cause -> do
            t1 <- whnf (f1 :$ sp1)
            go (t1 :===: t2 :@ cause)
          t1 :===: f2@(Free (Q (_ :.: _)) ::: _) :$ sp2 :@ cause -> do
            t2 <- whnf (f2 :$ sp2)
            go (t1 :===: t2 :@ cause)
          tm1 :===: Lam t2 b2 :@ cause -> do
            t1 <- ensurePi cause tm1
            (n, v) <- freshName t1
            go (lam (Q (Local n) ::: t1) (tm1 $$ v) :===: Lam t2 b2 :@ cause)
          Lam t1 b1 :===: tm2 :@ cause -> do
            t2 <- ensurePi cause tm2
            (n, v) <- freshName t2
            go (Lam t1 b1 :===: lam (Q (Local n) ::: t2) (tm2 $$ v) :@ cause)
          q@(t1 :===: t2 :@ cause)
            | stuck t1                 -> tell (Set.singleton q)
            | stuck t2                 -> tell (Set.singleton q)
            | span :| _ <- spans cause -> throwError (ElabError span mempty (TypeMismatch q))
        freshName t = ((,) <*> free . (::: t) . Q . Local) <$> gensym ""
        exists t = free . (::: t) . M . Meta <$> gensym "_meta_"

        typeof cause = infer
          where infer Type = pure Type
                infer (Pi _ _ t b) = do
                  t' <- check (t ::: Type)
                  (_, v) <- freshName t'
                  Type <$ check (instantiate v b ::: Type)
                infer (Lam t b) = do
                  t' <- check (t ::: Type)
                  (n, v) <- freshName t'
                  pi ((n, Ex, More) ::: t') <$> infer (instantiate v b)
                infer ((_ ::: ty) :$ sp) = pure (ty $$* sp)
                check (tm ::: ty) = do
                  ty' <- infer tm
                  if ty == ty' then pure ty' else do
                    m <- exists Type
                    m <$ tell (Set.fromList [m :===: ty :@ cause, m :===: ty' :@ cause])

        ensurePi cause = typeof cause >=> whnf >=> \case
          Pi _ _ t _ -> pure t
          (Free (M m) ::: ty) :$ sp -> do
            m1 <- M . Meta <$> gensym "_meta_"
            m2 <- M . Meta <$> gensym "_meta_"
            (names, _) <- unpis ty
            n <- gensym ""
            let t1 = pis names (free (m1 ::: Type))
                app ((n, _, _) ::: t) = free (Q (Local n) ::: t)
                t2 = pis (names :> ((n, Im, Zero) ::: free (m1 ::: Type) $$* fmap app names)) Type
                _A = free (m1 ::: t1) $$* sp
                _B x = free (m2 ::: t2) $$* (sp:>x)
            _A <$ tell (Set.singleton ((Free (M m) ::: ty) :$ sp :===: pi ((n, Im, More) ::: _A) (_B (free (Q (Local n) ::: _A))) :@ cause))
          t | span :| _ <- spans cause -> throwError (ElabError span mempty (IllegalApplication t))

        stuck ((Free (M _) ::: _) :$ _) = True
        stuck _                         = False

solve :: ( Carrier sig m
         , Effect sig
         , Member (Error ElabError) sig
         , Member (Reader Gensym) sig
         , Member (Reader Scope) sig
         , Monad m
         )
      => Set.Set (Caused (Equation Value))
      -> m [Caused Solution]
solve cs
  = local (// "solve")
  . runFresh
  . fmap (map (uncurry toSolution) . Map.toList)
  . execState mempty
  . evalState (Seq.empty :: Seq.Seq (Caused (Equation Value)))
  $ do
    stuck <- fmap fold . execState (mempty :: Map.Map Meta (Set.Set (Caused (Equation Value)))) $ do
      modify (flip (foldl' (Seq.|>)) cs)
      step
    unless (Prelude.null stuck) $ for_ stuck throwMismatch -- FIXME: throw a single error comprised of all of them
  where step = dequeue >>= \case
          Just q -> do
            _S <- get
            process _S q
            step
          Nothing -> pure ()

        process _S q@(t1 :===: t2 :@ c)
          | Just s <- solutions _S (metaNames (fvs t1 <> fvs t2)) = simplify (apply s q) >>= modify . flip (foldl' (Seq.|>))
          | Just (m, sp) <- pattern t1 = solve (m := lams sp t2 :@ c)
          | Just (m, sp) <- pattern t2 = solve (m := lams sp t1 :@ c)
          | otherwise = enqueue q

        enqueue q = do
          let s = Set.singleton q
              mvars = metaNames (fvs q)
          when (Prelude.null mvars) (throwMismatch q)
          modify (Map.unionWith (<>) (foldl' (\ m i -> Map.insertWith (<>) i s m) mempty mvars))

        dequeue = gets Seq.viewl >>= \case
          Seq.EmptyL -> pure Nothing
          h Seq.:< q -> Just h <$ put q

        pattern ((Free (M m) ::: _) :$ sp) = (,) m <$> traverse free sp
        pattern _                          = Nothing

        free ((Free v ::: t) :$ Nil) = Just (v ::: t)
        free _                       = Nothing

        solve (m := v :@ c) = do
          modify (Map.insert m (v :@ c))
          cs <- gets (fromMaybe mempty . Map.lookup m)
          modify (flip (foldl' (Seq.|>)) (cs :: Set.Set (Caused (Equation Value))))
          modify (Map.delete @Meta @(Set.Set (Caused (Equation Value))) m)

        solutions _S s
          | s:ss <- catMaybes (solution _S <$> Set.toList s) = Just (s:ss)
          | otherwise                                        = Nothing
        solution _S m = toSolution m <$> Map.lookup m _S

        toSolution m (v :@ c) = m := v :@ c

        throwMismatch q@(_ :@ c) | let span :| _ = spans c = throwError (ElabError span mempty (TypeMismatch q))
