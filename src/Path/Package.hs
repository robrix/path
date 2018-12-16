module Path.Package where

import Path.Name

data Package = Package
  { packageName        :: PackageName
  , packageConstraints :: [Constraint]
  , packageSources     :: [FilePath]
  }
  deriving (Eq, Ord, Show)

data Constraint
  = Depends PackageName
  deriving (Eq, Ord, Show)
