module Path.Package where

import Path.Module

type PackageName = String

data Package = Package
  { packageName        :: PackageName
  , packageSourceDir   :: FilePath
  , packageModules     :: [ModuleName]
  , packageConstraints :: [Constraint]
  }

data Constraint
  = Depends PackageName
