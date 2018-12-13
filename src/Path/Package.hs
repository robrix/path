module Path.Package where

import Path.Name

data Package = Package
  { packageName        :: PackageName
  , packageSourceDir   :: FilePath
  , packageModules     :: [ModuleName]
  , packageConstraints :: [Constraint]
  }

data Constraint
  = Depends PackageName
