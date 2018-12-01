module Path.Expr where

type Name = String

data Expr
  = Var Name
  | Abs Name Expr
  | App Expr Expr
  deriving (Eq, Ord, Show)

data Val
  = Closure Name Expr
  deriving (Eq, Ord, Show)
