module Path.Decl where

import Algebra.Graph.AdjacencyMap
import Data.List.NonEmpty
import Path.Surface
import Path.Term

data Decl
  = Declare String (Term Surface)
  | Define String (Term Surface)
  deriving (Eq, Ord, Show)

type ModuleName = NonEmpty String

data Module
  = Module ModuleName [Directive] [Decl]
  deriving (Eq, Ord, Show)

data Directive
  = Import ModuleName
  deriving (Eq, Ord, Show)


type ModuleGraph = AdjacencyMap ModuleName
