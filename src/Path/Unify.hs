module Path.Unify where

data Constraint
  = Top
  | Constraint :/\: Constraint
