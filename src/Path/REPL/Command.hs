{-# LANGUAGE TypeOperators #-}
module Path.REPL.Command where

import Path.Module
import Path.Name
import Path.Span (Spanned(..))
import Path.Surface

data Command
  = Quit
  | Help
  | TypeOf (Spanned (Surface User))
  | Decl (Decl (Surface User))
  | Eval (Spanned (Surface User))
  | Show Info
  | Reload
  | Import (Spanned ModuleName)
  | Doc ModuleName
  deriving (Eq, Ord, Show)

data Info
  = Bindings
  | Modules
  deriving (Eq, Ord, Show)
