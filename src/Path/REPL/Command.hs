module Path.REPL.Command where

import Path.Module
import Path.Name
import Path.Surface
import Path.Term
import Text.Trifecta.Rendering (Span)

data Command
  = Quit
  | Help
  | TypeOf (Term (Surface Name Name) Span)
  | Decl (Decl Name (Term (Surface Name Name) Span))
  | Eval (Term (Surface Name Name) Span)
  | Show Info
  | Reload
  | Import Import
  | Doc ModuleName
  deriving (Eq, Ord, Show)

data Info
  = Bindings
  | Modules
  deriving (Eq, Ord, Show)
