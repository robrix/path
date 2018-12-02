{-# LANGUAGE DeriveFunctor, KindSignatures #-}
module Path.Elab where

import Path.Expr

data Elaborate (m :: * -> *) k
  = Infer (Term Surface) (Elab -> k)
  | Check (Term Surface) Type (Elab -> k)
  | Define Elab k
  deriving (Functor)
