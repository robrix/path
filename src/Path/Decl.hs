module Path.Decl where

import Data.List.NonEmpty
import Path.Surface
import Path.Term

data Decl
  = Declare String (Term Surface)
  | Define String (Term Surface)
  deriving (Eq, Ord, Show)

data Module
  = Module (NonEmpty String) [Decl]
  deriving (Eq, Ord, Show)
