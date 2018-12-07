module Path.Package where

import Path.Module

type PackageName = String

data Package = Package
  { packageName        :: PackageName
  , packageModules     :: [ModuleName]
  , packageConstraints :: [Constraint]
  }

data Constraint
  = Depends PackageName
