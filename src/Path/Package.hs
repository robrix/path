module Path.Package where

import Path.Name

data Package = Package
  { packageName        :: PackageName
  , packageSourceDir   :: FilePath
  , packageModules     :: [ModuleName]
  , packageConstraints :: [Constraint]
  }
  deriving (Eq, Ord, Show)

data Constraint
  = Depends PackageName
  deriving (Eq, Ord, Show)
