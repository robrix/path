module Path.Unify where

data Twin = Only | TwinL | TwinR
  deriving (Eq, Ord, Show)

data Equation a = a :==: a
  deriving (Eq, Ord, Show)
