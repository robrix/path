{-# LANGUAGE LambdaCase, MultiParamTypeClasses #-}
module Path.Surface where

import Path.Name
import Path.Plicity
import Path.Usage
import Text.Trifecta.Rendering (Spanned)

data Surface
  = Var User
  | Lam (Plicit (Maybe User)) (Spanned Surface)
  | Spanned Surface :$ Plicit (Spanned Surface)
  | Type
  | Pi (Plicit (Maybe User, Usage, Spanned Surface)) (Spanned Surface)
  | Hole (Maybe String)
  | (Usage, Spanned Surface) :-> Spanned Surface
  deriving (Eq, Ord, Show)

infixr 0 :->
