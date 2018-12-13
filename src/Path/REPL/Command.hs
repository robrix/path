module Path.REPL.Command where

import Path.Decl
import Path.Module
import Path.Name
import Path.Surface
import Path.Term
import Text.Trifecta.Rendering (Span)

data Command
  = Quit
  | Help
  | TypeOf (Term (Surface Name) Span)
  | Decl (Decl (Term (Surface Name) Span))
  | Eval (Term (Surface Name) Span)
  | Show Info
  | Load ModuleName
  | Reload
  | Import Import
  deriving (Eq, Ord, Show)

data Info
  = Bindings
  deriving (Eq, Ord, Show)
