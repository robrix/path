{-# LANGUAGE RankNTypes #-}
module Path.Term where

import Control.Effect.Carrier
import Path.Scope

data Term sig a
  = Var a
  | Term (sig (Term sig) a)


class HFunctor sig => Syntax sig where
  foldSyntax :: (forall x y . (x -> m y) -> f x -> n y)
             -> (forall a . Incr () (n a) -> m (Incr () (n a)))
             -> (a -> m b)
             -> sig f a
             -> sig n b
