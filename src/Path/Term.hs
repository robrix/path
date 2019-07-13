module Path.Term where

data Term sig a
  = Var a
  | Term (sig (Term sig) a)
