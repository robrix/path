module Path.REPL.Command where

import Path.Module
import Path.Name
import Path.Surface
import Text.Trifecta.Rendering (Spanned(..))

data Command
  = Quit
  | Help
  | TypeOf Surface
  | Decl (Spanned (Decl User Surface))
  | Eval Surface
  | Show Info
  | Reload
  | Import Import
  | Doc ModuleName
  deriving (Eq, Ord, Show)

data Info
  = Bindings
  | Modules
  deriving (Eq, Ord, Show)
