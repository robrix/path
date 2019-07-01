{-# LANGUAGE TypeOperators #-}
module Path.Surface where

import Path.Name
import Path.Plicity
import Path.Usage
import Text.Trifecta.Rendering (Spanned)

data Surface
  = Var User
  | Lam (Plicit User) (Spanned Surface)
  | Spanned Surface :$ Plicit (Spanned Surface)
  | Type
  | Pi (Plicit (User ::: Used (Spanned Surface))) (Spanned Surface)
  | Hole (Maybe String)
  deriving (Eq, Ord, Show)

(-->) :: Used (Spanned Surface) -> Spanned Surface -> Surface
t --> b = Pi (Ex :< Unused ::: t) b

infixr 0 -->
