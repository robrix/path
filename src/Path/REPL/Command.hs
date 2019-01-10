module Path.REPL.Command where

import Path.Module
import Path.Name
import Path.Surface
import Path.Term

data Command
  = Quit
  | Help
  | TypeOf (Term (Surface (Maybe UName) UName))
  | Decl (Decl UName (Term (Surface (Maybe UName) UName)))
  | Eval (Term (Surface (Maybe UName) UName))
  | Show Info
  | Reload
  | Import Import
  | Doc ModuleName
  deriving (Eq, Ord, Show)

data Info
  = Bindings
  | Modules
  deriving (Eq, Ord, Show)
