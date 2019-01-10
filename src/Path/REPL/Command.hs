module Path.REPL.Command where

import Path.Module
import Path.Name
import Path.Surface
import Path.Term
import Text.Trifecta.Rendering (Span)

data Command
  = Quit
  | Help
  | TypeOf (Term (Surface (Maybe UName) UName) Span)
  | Decl (Decl UName (Term (Surface (Maybe UName) UName) Span))
  | Eval (Term (Surface (Maybe UName) UName) Span)
  | Show Info
  | Reload
  | Import Import
  | Doc ModuleName
  deriving (Eq, Ord, Show)

data Info
  = Bindings
  | Modules
  deriving (Eq, Ord, Show)
