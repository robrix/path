{-# LANGUAGE TypeOperators #-}
module Path.REPL.Command where

import Path.Module
import Path.Name
import Path.Span (Spanned(..))
import Path.Surface

data Command
  = Quit
  | Help
  | TypeOf (Spanned (Surface Var))
  | Decl (Spanned (Decl User (Spanned (Surface Var) ::: Spanned (Surface Var))))
  | Eval (Spanned (Surface Var))
  | Show Info
  | Reload
  | Import (Spanned Import)
  | Doc ModuleName
  deriving (Eq, Ord, Show)

data Info
  = Bindings
  | Modules
  deriving (Eq, Ord, Show)
