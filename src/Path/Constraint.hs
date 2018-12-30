{-# LANGUAGE DeriveFunctor, TypeOperators #-}
module Path.Constraint where

import Path.Context
import Path.Name

data Constraint
  = Top
  | Constraint :/\: Constraint
  | Int :=: Int
  | Exists Int Constraint
  | Instance Name Int
  | Def Name Int Constraint
  | Let Name Int Constraint Constraint
  | Int :@ (Type QName)

data Witness = Witness

data Solver m a = Solver Constraint (Witness -> m a)
  deriving (Functor)

instance Applicative m => Applicative (Solver m) where
  pure a = Solver Top (const (pure a))

  Solver c1 f <*> Solver c2 a = Solver (c1 :/\: c2) ((<*>) <$> f <*> a)
