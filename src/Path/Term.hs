module Path.Term where

data Term f a
  = Var a
  | Term (f (Term f) a)
