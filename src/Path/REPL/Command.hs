module Path.REPL.Command where

import Path.Module
import Path.Name
import Path.Surface

data Command
  = Quit
  | Help
  | TypeOf Surface
  | Decl (Decl UName Surface)
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
