module Path.Package where

import Path.Module

newtype PackageName = PackageName String

data Package = Package
  { packageName        :: PackageName
  , packageModules     :: [ModuleName]
  , packageConstraints :: [Constraint]
  }

data Constraint
  = Depends PackageName
