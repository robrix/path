{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Solver where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.State
import Data.Foldable (for_)
import qualified Data.Sequence as Seq
import qualified Data.Map as Map
import qualified Data.Set as Set
import Path.Constraint
import Path.Error
import Path.Name
import Path.Value

simplify :: (Carrier sig m, Member (Error ElabError) sig, Member Fresh sig, Monad m) => Caused (Equation (Typed Value)) -> m (Set.Set (Caused (Equation (Typed Value))))
simplify = \case
  tm1 ::: ty1 :===: tm2 ::: ty2 :@ _ | ty1 == ty2, tm1 == tm2 -> pure Set.empty
  Pi p1 u1 t1 b1 ::: Type :===: Pi p2 u2 t2 b2 ::: Type :@ cause
    | p1 == p2, u1 == u2 -> do
      n <- freshName "_unify_" t1
      let vn = vfree n
      (<>) <$> simplify (t1    ::: Type :===: t2    ::: Type :@ cause)
           <*> simplify (b1 vn ::: Type :===: b2 vn ::: Type :@ cause)
  f1 ::: Pi p1 u1 t1 b1 :===: f2 ::: Pi p2 u2 t2 b2 :@ cause
    | p1 == p2, u1 == u2 -> do
      n <- freshName "_unify_" t1
      let vn = vfree n
      (<>) <$> simplify (t1       ::: Type  :===: t2       ::: Type  :@ cause)
           <*> simplify (f1 $$ vn ::: b1 vn :===: f2 $$ vn ::: b2 vn :@ cause)
  q@(t1 :===: t2) :@ cause
    | stuck t1  -> pure (Set.singleton (q :@ cause))
    | stuck t2  -> pure (Set.singleton (q :@ cause))
    | otherwise -> throwError (ElabError (spans cause) mempty (TypeMismatch q))
  where freshName s t = (::: t) . Local . Gensym s <$> fresh
        stuck ((Meta _ ::: _) :$ _ ::: _) = True
        stuck _                           = False

solve :: (Carrier sig m, Effect sig, Member (Error ElabError) sig, Member Fresh sig, Monad m) => Set.Set (Caused (Equation (Typed Value))) -> m [Caused Solution]
solve = fmap (map (uncurry toSolution) . Map.toList) . execState mempty . evalState (Seq.empty :: Seq.Seq (Caused (Equation (Typed Value)))) . visit
  where visit cs = for_ cs each
        each q@(s1 :===: s2 :@ _) = do
          _S <- get
          case () of
            _ | Just sol <- stuck s1 >>= solved _S -> simplify (apply [sol] q) >>= visit
              | Just sol <- stuck s2 >>= solved _S -> simplify (apply [sol] q) >>= visit
              | otherwise -> modify (Seq.|> q)

        stuck ((Meta m ::: _) :$ _ ::: _) = Just m
        stuck _                           = Nothing

        solved _S m = case Map.lookup m _S of
          Just t  -> Just (toSolution m t)
          Nothing -> Nothing

        toSolution m (v ::: t :@ c) = m := v ::: t :@ c
