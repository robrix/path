module Path.REPL.Command where

import Path.Decl
import Path.Module
import Path.Surface
import Path.Term
import Text.Trifecta.Rendering (Span)

data Command
  = Quit
  | Help
  | TypeOf (Term Surface Span)
  | Decl (Decl (Term Surface Span))
  | Eval (Term Surface Span)
  | Show Info
  | Load ModuleName
  | Reload
  deriving (Eq, Ord, Show)

data Info
  = Bindings
  deriving (Eq, Ord, Show)
