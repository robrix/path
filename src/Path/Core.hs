{-# LANGUAGE LambdaCase #-}
module Path.Core where

import Path.Name
import Path.Plicity
import Path.Usage
import Prelude hiding (pi)
import Text.Trifecta.Rendering (Span)

data Core
  = Var (Name Local)
  | Lam (Maybe User) Core
  | Core :$ Core
  | Type
  | Pi (Maybe User) Plicity Usage Core Core
  | Hole User
  | Ann Span Core
  deriving (Eq, Ord, Show)
