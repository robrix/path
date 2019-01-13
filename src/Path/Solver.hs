{-# LANGUAGE FlexibleContexts, LambdaCase, TypeApplications #-}
module Path.Solver where

import           Control.Effect
import           Control.Effect.Error
import           Control.Effect.Fresh
import           Control.Effect.Reader hiding (Local)
import           Control.Effect.State
import           Control.Effect.Writer
import           Control.Monad ((>=>))
import           Data.Foldable (foldl', for_, toList)
import qualified Data.IntMap as IntMap
import           Data.List.NonEmpty (NonEmpty (..))
import           Data.Maybe (catMaybes)
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
  where go = local prime . \case
          tm1 :===: tm2 :@ _ | tm1 == tm2 -> pure ()
          Pi p1 u1 t1 b1 :===: Pi p2 u2 t2 b2 :@ cause
            | p1 == p2, u1 == u2 -> do
              (_, n) <- freshName "_unify_" t1
              go (t1               :===: t2               :@ cause)
              go (instantiate n b1 :===: instantiate n b2 :@ cause)
          Pi Im _ ty1 b1 :===: t2 :@ cause -> do
            n <- exists ty1
            go (instantiate n b1 :===: t2 :@ cause)
          t1 :===: Pi Im _ ty2 b2 :@ cause -> do
            n <- exists ty2
            go (t1 :===: instantiate n b2 :@ cause)
          Lam t1 b1 :===: Lam t2 b2 :@ cause -> do
            (_, n) <- freshName "_unify_" t1
            go (t1               :===: t2               :@ cause)
            go (instantiate n b1 :===: instantiate n b2 :@ cause)
          (f1 ::: tf1) :$ sp1 :===: (f2 ::: tf2) :$ sp2 :@ cause
            | f1 == f2, length sp1 == length sp2 -> do
              go (tf1 :===: tf2 :@ cause)
              for_ (zipWith (:===:) (toList sp1) (toList sp2)) (go . (:@ cause))
          f1@(Free (_ :.: _) ::: _) :$ sp1 :===: f2@(Free (_ :.: _) ::: _) :$ sp2 :@ cause -> do
            t1 <- whnf (f1 :$ sp1)
            t2 <- whnf (f2 :$ sp2)
            go (t1 :===: t2 :@ cause)
          f1@(Free (_ :.: _) ::: _) :$ sp1 :===: t2 :@ cause -> do
            t1 <- whnf (f1 :$ sp1)
            go (t1 :===: t2 :@ cause)
          t1 :===: f2@(Free (_ :.: _) ::: _) :$ sp2 :@ cause -> do
            t2 <- whnf (f2 :$ sp2)
            go (t1 :===: t2 :@ cause)
          tm1 :===: Lam t2 b2 :@ cause -> do
            t1 <- ensurePi cause tm1
            (n, v) <- freshName "_unify_" t1
            go (lam (n ::: t1) (tm1 $$ v) :===: Lam t2 b2 :@ cause)
          Lam t1 b1 :===: tm2 :@ cause -> do
            t2 <- ensurePi cause tm2
            (n, v) <- freshName "_unify_" t2
            go (Lam t1 b1 :===: lam (n ::: t2) (tm2 $$ v) :@ cause)
          q@(t1 :===: t2 :@ cause)
            | stuck t1                 -> tell (Set.singleton q)
            | stuck t2                 -> tell (Set.singleton q)
            | span :| _ <- spans cause -> throwError (ElabError span mempty (TypeMismatch q))
        freshName s t = asks (((,) <*> free . (::: t) . Local) . (// s))
        exists t = free . (::: t) . Meta . M <$> fresh

        typeof cause = infer
          where infer Type = pure Type
                infer (Pi _ _ t b) = do
                  (_, v) <- freshName "_infer_" t
                  Type <$ check (t ::: Type) <* check (instantiate v b ::: Type)
                infer (Lam t b) = do
                  t' <- check (t ::: Type)
                  (n, v) <- freshName "_infer_" t'
                  pi ((n, Ex, More) ::: t') <$> infer (instantiate v b)
                infer ((_ ::: ty) :$ sp) = pure (ty $$* sp)
                check (tm ::: ty) = do
                    ty' <- infer tm
                    if ty == ty' then pure ty' else do
                      m <- exists Type
                      m <$ tell (Set.fromList [m :===: ty :@ cause, m :===: ty' :@ cause])

        ensurePi cause = typeof cause >=> whnf >=> \case
          Pi _ _ t _ -> pure t
          (Free (Meta m) ::: ty) :$ sp -> do
            m1 <- Meta . M <$> fresh
            m2 <- Meta . M <$> fresh
            n <- asks (// "ensurePi")
            let t1 = pis (fst (unpis n ty)) (free (m1 ::: Type))
                maximal Nil                      = n
                maximal (_ :> ((n, _, _) ::: _)) = n
                app ((n, _, _) ::: t) = free (Local n ::: t)
                t2 = let (s, _) = unpis n ty in pis (s :> ((maximal s, Im, Zero) ::: free (m1 ::: Type) $$* fmap app s)) Type
                _A = free (m1 ::: t1) $$* sp
                _B x = free (m2 ::: t2) $$* (sp:>x)
            _A <$ tell (Set.singleton ((Free (Meta m) ::: ty) :$ sp :===: pi ((n, Im, More) ::: _A) (_B (free (Local n ::: _A))) :@ cause))
          t | span :| _ <- spans cause -> throwError (ElabError span mempty (IllegalApplication t))

        stuck ((Free (Meta _) ::: _) :$ _) = True
        stuck _                            = False

solve :: ( Carrier sig m
         , Effect sig
         , Member (Error ElabError) sig
         , Member Fresh sig
         , Member (Reader Gensym) sig
         , Member (Reader Scope) sig
         , Monad m
         )
      => Set.Set (Caused (Equation Value))
      -> m [Caused Solution]
solve cs
  = fmap (map (uncurry toSolution) . IntMap.toList)
  . execState mempty
  . evalState (Seq.empty :: Seq.Seq (Caused (Equation Value)))
  . evalState (mempty :: IntMap.IntMap (Set.Set (Caused (Equation Value))))
  $ do
    modify (flip (foldl' (Seq.|>)) cs)
    step
  where visit cs = for_ cs each
        each q@(t1 :===: t2 :@ c) = do
          _S <- get
          case () of
            _ | Just s <- solutions _S (metaNames (fvs t1 <> fvs t2)) -> simplify (apply s q) >>= visit
              | Just (m, sp) <- pattern t1 -> solve (m := abstractLam sp t2 :@ c)
              | Just (m, sp) <- pattern t2 -> solve (m := abstractLam sp t1 :@ c)
              | otherwise -> enqueue q

        step = do
          c <- dequeue
          case c of
            Just c  -> each c *> step
            Nothing -> pure ()

        enqueue q = do
          let s = Set.singleton q
              mvars = metaNames (fvs q)
          modify (Seq.|> q)
          modify (IntMap.unionWith (<>) (foldl' (\ m (M i) -> IntMap.insertWith (<>) i s m) mempty mvars))

        dequeue = do
          q <- get
          case Seq.viewl q of
            Seq.EmptyL -> pure Nothing
            h Seq.:< q -> Just h <$ put q

        pattern ((Free (Meta m) ::: _) :$ sp) = (,) m <$> traverse free sp
        pattern _                             = Nothing

        free ((Free v ::: t) :$ Nil) = Just (v ::: t)
        free _                       = Nothing

        solve s@(M m := v :@ c) = do
          modify (IntMap.insert m (v :@ c))
          modify (IntMap.adjust (apply @(Set.Set (Caused (Equation Value))) [s]) m)

        solutions _S s
          | (s:ss) <- catMaybes (solution _S <$> Set.toList s) = Just (s:ss)
          | otherwise                                          = Nothing
        solution _S (M m) = toSolution m <$> IntMap.lookup m _S

        toSolution m (v :@ c) = M m := v :@ c
