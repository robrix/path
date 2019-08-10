module Path.Nat where

data Nat = Z | S Nat
  deriving (Eq, Ord, Show)
