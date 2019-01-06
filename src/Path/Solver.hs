{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Solver where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Fresh
import qualified Data.Set as Set
import Path.Constraint
import Path.Error
import Path.Name
import Path.Value
import Text.Trifecta.Rendering (Span)

simplify :: (Carrier sig m, Member (Error ElabError) sig, Member Fresh sig, Monad m) => Span -> Equation -> m (Set.Set Equation)
simplify span = \case
  tm1 ::: ty1 :===: tm2 ::: ty2 | ty1 == ty2, tm1 == tm2 -> pure Set.empty
  Pi p1 u1 t1 b1 ::: Type :===: Pi p2 u2 t2 b2 ::: Type
    | p1 == p2, u1 == u2 -> do
      n <- freshName "_unify_" t1
      let vn = vfree n
      (<>) <$> simplify span (t1    ::: Type :===: t2    ::: Type)
           <*> simplify span (b1 vn ::: Type :===: b2 vn ::: Type)
  f1 ::: Pi p1 u1 t1 b1 :===: f2 ::: Pi p2 u2 t2 b2
    | p1 == p2, u1 == u2 -> do
      n <- freshName "_unify_" t1
      let vn = vfree n
      (<>) <$> simplify span (t1       ::: Type  :===: t2       ::: Type)
           <*> simplify span (f1 $$ vn ::: b1 vn :===: f2 $$ vn ::: b2 vn)
  q -> throwError (ElabError span mempty (TypeMismatch q))
  where freshName s t = (::: t) . Local . Gensym s <$> fresh

solve :: Monad m => Set.Set (Equation, Cause) -> m (Value -> Value)
solve equations = case Set.minView equations of
  Nothing -> pure id
  Just _  -> pure id
