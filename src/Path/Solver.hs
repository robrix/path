{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Solver where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.State
import Data.Foldable (for_, toList)
import qualified Data.Sequence as Seq
import qualified Data.Map as Map
import qualified Data.Set as Set
import Path.Back
import Path.Constraint
import Path.Error
import Path.Eval
import Path.Name
import Path.Plicity
import Path.Scope
import Path.Usage
import Path.Value

simplify :: (Carrier sig m, Member (Error ElabError) sig, Member Fresh sig, Member (Reader Scope) sig, Monad m) => Caused (Equation (Typed Value)) -> m (Set.Set (Caused (Equation (Typed Value))))
simplify = \case
  tm1 ::: ty1 :===: tm2 ::: ty2 :@ _ | ty1 == ty2, tm1 == tm2 -> pure Set.empty
  Pi p1 u1 t1 b1 ::: Type :===: Pi p2 u2 t2 b2 ::: Type :@ cause
    | p1 == p2, u1 == u2 -> do
      n <- freshName "_unify_" t1
      let vn = vfree n
      (<>) <$> simplify (t1    ::: Type :===: t2    ::: Type :@ cause)
           <*> simplify (b1 vn ::: Type :===: b2 vn ::: Type :@ cause)
  Pi Im _ ty1 b1 ::: Type :===: t2 ::: Type :@ cause -> do
    n <- exists ty1
    simplify (b1 n ::: Type :===: t2 ::: Type :@ cause)
  t1 ::: Type :===: Pi Im _ ty2 b2 ::: Type :@ cause -> do
    n <- exists ty2
    simplify (t1 ::: Type :===: b2 n ::: Type :@ cause)
  f1 ::: Pi p1 u1 t1 b1 :===: f2 ::: Pi p2 u2 t2 b2 :@ cause
    | p1 == p2, u1 == u2 -> do
      n <- freshName "_unify_" t1
      let vn = vfree n
      (<>) <$> simplify (t1       ::: Type  :===: t2       ::: Type  :@ cause)
           <*> simplify (f1 $$ vn ::: b1 vn :===: f2 $$ vn ::: b2 vn :@ cause)
  q@((f1 ::: tf1) :$ sp1 ::: _ :===: (f2 ::: tf2) :$ sp2 ::: _ :@ cause)
    | f1 == f2, length sp1 == length sp2 -> do
      (<>) <$> simplify (tf1 ::: Type :===: tf2 ::: Type :@ cause)
           <*> simplifySpines q tf1 (zip (toList sp1) (toList sp2))
  (f1@((_ :.: _) ::: _) :$ sp1 ::: ty1 :===: t2 ::: ty2 :@ cause) -> do
    t1 <- whnf (f1 :$ sp1)
    simplify (t1 ::: ty1 :===: t2 ::: ty2 :@ cause)
  (t1 ::: ty1 :===: f2@((_ :.: _) ::: _) :$ sp2 ::: ty2 :@ cause) -> do
    t2 <- whnf (f2 :$ sp2)
    simplify (t1 ::: ty1 :===: t2 ::: ty2 :@ cause)
  tm1 ::: ty1 :===: Lam t2 b2 ::: ty2 :@ cause -> do
    (u, t1, b1, s) <- ensurePi cause ty1
    (<> s) <$> simplify (Lam t1 (tm1 $$) ::: Pi Im u t1 b1 :===: Lam t2 b2 ::: ty2 :@ cause)
  Lam t1 b1 ::: ty1 :===: tm2 ::: ty2 :@ cause -> do
    (u, t2, b2, s) <- ensurePi cause ty2
    (<> s) <$> simplify (Lam t1 b1 ::: ty1 :===: Lam t2 (tm2 $$) ::: Pi Im u t2 b2 :@ cause)
  q@(t1 :===: t2) :@ cause
    | stuck t1  -> pure (Set.singleton (q :@ cause))
    | stuck t2  -> pure (Set.singleton (q :@ cause))
    | otherwise -> throwError (ElabError (spans cause) mempty (TypeMismatch q))
  where freshName s t = (::: t) . Local . Gensym s <$> fresh
        exists t = vfree . (::: t) . Meta . M <$> fresh

        ensurePi cause t = whnf t >>= \ t -> case t of
          Pi _ pi t b -> pure (pi, t, b, Set.empty)
          (Meta _ ::: ty) :$ sp -> do
            m1 <- Meta . M <$> fresh
            m2 <- Meta . M <$> fresh
            let recur1 (Pi p u t b) = Pi p u t (\ x -> recur1 (b x))
                recur1 _            = vfree (m1 ::: Type)
                t1 = recur1 ty
                recur2 (Pi p u t b) xs = Pi p u t (\ x -> recur2 (b x) (xs :> x))
                recur2 _            xs = Pi Im Zero (vfree (m1 ::: Type) $$* xs) (const Type)
                t2 = recur2 ty Nil
                _A = vfree (m1 ::: t1) $$* sp
                _B x = vfree (m2 ::: t2) $$* (sp:>x)
            pure (More, _A, _B, Set.singleton (t ::: Type :===: Pi Im More _A _B ::: Type :@ cause))
          _ -> throwError (ElabError (spans cause) mempty (IllegalApplication t))

        stuck ((Meta _ ::: _) :$ _ ::: _) = True
        stuck _                           = False

        simplifySpines _        _            []            = pure Set.empty
        simplifySpines (q :@ c) (Pi _ _ t b) ((a1, a2):as) = (<>) <$> simplify (a1 ::: t :===: a2 ::: t :@ c) <*> simplifySpines (q :@ c) (b a1) as
        simplifySpines (q :@ c) _            _             = throwError (ElabError (spans c) mempty (TypeMismatch q))

solve :: (Carrier sig m, Effect sig, Member (Error ElabError) sig, Member Fresh sig, Member (Reader Scope) sig, Monad m) => Set.Set (Caused (Equation (Typed Value))) -> m [Caused Solution]
solve = fmap (map (uncurry toSolution) . Map.toList) . execState mempty . evalState (Seq.empty :: Seq.Seq (Caused (Equation (Typed Value)))) . visit
  where visit cs = for_ cs each
        each q@(t1 ::: ty1 :===: t2 ::: ty2 :@ c) = do
          _S <- get
          case () of
            _ | Just sol <- stuck t1 >>= solved _S -> simplify (apply [sol] q) >>= visit
              | Just sol <- stuck t2 >>= solved _S -> simplify (apply [sol] q) >>= visit
              | Just (m, sp) <- pattern t1 -> solve (m := abstractLam sp t2 ::: ty1 :@ c)
              | Just (m, sp) <- pattern t2 -> solve (m := abstractLam sp t1 ::: ty2 :@ c)
              | otherwise -> modify (Seq.|> q)

        stuck ((Meta m ::: _) :$ _) = Just m
        stuck _                     = Nothing

        pattern ((Meta m ::: _) :$ sp)
          | Just sp' <- traverse free sp = Just (m, sp')
        pattern _                        = Nothing

        free ((v ::: t) :$ Nil) = Just (v ::: t)
        free _                  = Nothing

        solve (m := v ::: t :@ c) = modify (Map.insert m (v ::: t :@ c))

        solved _S m = case Map.lookup m _S of
          Just t  -> Just (toSolution m t)
          Nothing -> Nothing

        toSolution m (v ::: t :@ c) = m := v ::: t :@ c
