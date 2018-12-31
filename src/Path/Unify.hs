module Path.Unify where

data Constraint
  = Top
  | Constraint :/\: Constraint
  deriving (Eq, Ord, Show)
