module Path.Expr where

data Expr
  = Lam (Expr -> Expr)
  | App Expr Expr
