module Path.Expr where

data Expr
  = Lam (Expr -> Expr)
  | App Expr Expr


type Name = String

data Val
  = Closure Name (Expr -> Expr)
