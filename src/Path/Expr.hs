module Path.Expr where

type Name = String

data Expr
  = Var Name
  | Abs Name Expr
  | App Expr Expr

data Val
  = Closure Name Expr
