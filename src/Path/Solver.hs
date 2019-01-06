{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Solver where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.State
import Control.Effect.Writer
import Data.Foldable (for_, toList)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
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

simplify :: (Carrier sig m, Effect sig, Member (Error ElabError) sig, Member Fresh sig, Member (Reader Scope) sig, Monad m) => Caused (Equation Value) -> m (Set.Set (Caused (Equation Value)))
simplify = execWriter . go
  where go = \case
          tm1 :===: tm2 :@ _ | tm1 == tm2 -> pure ()
          Pi p1 u1 t1 b1 :===: Pi p2 u2 t2 b2 :@ cause
            | p1 == p2, u1 == u2 -> do
              (_, n) <- freshName "_unify_" t1
              go (t1   :===: t2   :@ cause)
              go (b1 n :===: b2 n :@ cause)
          Pi Im _ ty1 b1 :===: t2 :@ cause -> do
            n <- exists ty1
            go (b1 n :===: t2 :@ cause)
          t1 :===: Pi Im _ ty2 b2 :@ cause -> do
            n <- exists ty2
            go (t1 :===: b2 n :@ cause)
          Lam t1 b1 :===: Lam t2 b2 :@ cause -> do
            (_, n) <- freshName "_unify_" t1
            go (t1   :===: t2   :@ cause)
            go (b1 n :===: b2 n :@ cause)
          (f1 ::: tf1) :$ sp1 :===: (f2 ::: tf2) :$ sp2 :@ cause
            | f1 == f2, length sp1 == length sp2 -> do
              go (tf1 :===: tf2 :@ cause)
              for_ (zipWith (:===:) (toList sp1) (toList sp2)) (go . (:@ cause))
          f1@((_ :.: _) ::: _) :$ sp1 :===: f2@((_ :.: _) ::: _) :$ sp2 :@ cause -> do
            t1 <- whnf (f1 :$ sp1)
            t2 <- whnf (f2 :$ sp2)
            go (t1 :===: t2 :@ cause)
          f1@((_ :.: _) ::: _) :$ sp1 :===: t2 :@ cause -> do
            t1 <- whnf (f1 :$ sp1)
            go (t1 :===: t2 :@ cause)
          t1 :===: f2@((_ :.: _) ::: _) :$ sp2 :@ cause -> do
            t2 <- whnf (f2 :$ sp2)
            go (t1 :===: t2 :@ cause)
          tm1 :===: Lam t2 b2 :@ cause -> do
            t1 <- ensurePi cause tm1
            go (Lam t1 (tm1 $$) :===: Lam t2 b2 :@ cause)
          Lam t1 b1 :===: tm2 :@ cause -> do
            t2 <- ensurePi cause tm2
            go (Lam t1 b1 :===: Lam t2 (tm2 $$) :@ cause)
          q@(t1 :===: t2 :@ cause)
            | stuck t1                 -> tell (Set.singleton q)
            | stuck t2                 -> tell (Set.singleton q)
            | span :| _ <- spans cause -> throwError (ElabError span mempty (TypeMismatch q))
        freshName s t = ((,) <*> vfree . (::: t)) . Local . Gensym s <$> fresh
        exists t = vfree . (::: t) . Meta . M <$> fresh

        typeof cause = infer
          where infer Type = pure Type
                infer (Pi _ _ t b) = do
                  (_, v) <- freshName "_infer_" t
                  Type <$ check (t ::: Type) <* check (b v ::: Type)
                infer (Lam t b) = do
                  t' <- check (t ::: Type)
                  (n, v) <- freshName "_infer_" t'
                  Pi Ex More t' . flip (subst n) <$> infer (b v)
                infer ((_ ::: ty) :$ sp) = pure (ty $$* sp)
                check (tm ::: ty) = do
                    ty' <- infer tm
                    if ty == ty' then pure ty' else do
                      m <- exists Type
                      m <$ tell (Set.fromList [m :===: ty :@ cause, m :===: ty' :@ cause])

        ensurePi cause t = typeof cause t >>= whnf >>= \ t -> case t of
          Pi _ _ t _ -> pure t
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
            _A <$ tell (Set.singleton (t :===: Pi Im More _A _B :@ cause))
          _ | span :| _ <- spans cause -> throwError (ElabError span mempty (IllegalApplication t))

        stuck ((Meta _ ::: _) :$ _) = True
        stuck _                     = False

solve :: (Carrier sig m, Effect sig, Member (Error ElabError) sig, Member Fresh sig, Member (Reader Scope) sig, Monad m) => Set.Set (Caused (Equation Value)) -> m [Caused Solution]
solve = fmap (map (uncurry toSolution) . Map.toList) . execState mempty . evalState (Seq.empty :: Seq.Seq (Caused (Equation Value))) . visit
  where visit cs = for_ cs each
        each q@(t1 :===: t2 :@ c) = do
          _S <- get
          case () of
            _ | Just sol <- stuck t1 >>= solved _S -> simplify (apply [sol] q) >>= visit
              | Just sol <- stuck t2 >>= solved _S -> simplify (apply [sol] q) >>= visit
              | Just (m, sp) <- pattern t1 -> solve (m := abstractLam sp t2 :@ c)
              | Just (m, sp) <- pattern t2 -> solve (m := abstractLam sp t1 :@ c)
              | otherwise -> modify (Seq.|> q)

        stuck ((Meta m ::: _) :$ _) = Just m
        stuck _                     = Nothing

        pattern ((Meta m ::: _) :$ sp)
          | Just sp' <- traverse free sp = Just (m, sp')
        pattern _                        = Nothing

        free ((v ::: t) :$ Nil) = Just (v ::: t)
        free _                  = Nothing

        solve (m := v :@ c) = modify (Map.insert m (v :@ c))

        solved _S m = case Map.lookup m _S of
          Just t  -> Just (toSolution m t)
          Nothing -> Nothing

        toSolution m (v :@ c) = m := v :@ c
