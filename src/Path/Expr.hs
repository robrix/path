module Path.Expr where

type Name = String

data Expr
  = Lam (Expr -> Expr)
  | App Expr Expr

data Val
  = Closure Name (Expr -> Expr)
