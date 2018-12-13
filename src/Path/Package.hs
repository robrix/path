module Path.Package where

import Path.Name

type PackageName = String

data Package = Package
  { packageName        :: PackageName
  , packageSourceDir   :: FilePath
  , packageModules     :: [ModuleName]
  , packageConstraints :: [Constraint]
  }

data Constraint
  = Depends PackageName
