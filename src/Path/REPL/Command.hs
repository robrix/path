{-# LANGUAGE TypeOperators #-}
module Path.REPL.Command where

import Path.Module
import Path.Name
import Path.Surface
import Text.Trifecta.Rendering (Spanned(..))

data Command
  = Quit
  | Help
  | TypeOf (Spanned (Surface User))
  | Decl (Spanned (Decl User (Spanned (Surface User) ::: Spanned (Surface User))))
  | Eval (Spanned (Surface User))
  | Show Info
  | Reload
  | Import (Spanned Import)
  | Doc ModuleName
  deriving (Eq, Ord, Show)

data Info
  = Bindings
  | Modules
  deriving (Eq, Ord, Show)
