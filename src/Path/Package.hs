module Path.Package where

import Path.Name

data Package = Package
  { packageName        :: PackageName
  , packageSources     :: [FilePath]
  , packageConstraints :: [Constraint]
  }
  deriving (Eq, Ord, Show)

data Constraint
  = Depends PackageName
  deriving (Eq, Ord, Show)
