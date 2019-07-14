{-# LANGUAGE TypeOperators #-}
module Path.REPL.Command where

import Path.Module
import Path.Name
import Path.Span (Spanned(..))
import Path.Surface
import Path.Term

data Command
  = Quit
  | Help
  | TypeOf (Spanned (Term Surface User))
  | Decl (Decl (Term Surface User))
  | Eval (Spanned (Term Surface User))
  | ShowModules
  | Reload
  | Import (Spanned ModuleName)
  | Doc (Spanned ModuleName)
  deriving (Eq, Ord, Show)
