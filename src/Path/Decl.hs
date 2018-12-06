module Path.Decl where

import Data.List.NonEmpty
import Path.Surface
import Path.Term

data Decl
  = Declare String (Term Surface)
  | Define String (Term Surface)
  deriving (Eq, Ord, Show)

type ModuleName = NonEmpty String

data Module
  = Module ModuleName [Decl]
  deriving (Eq, Ord, Show)
