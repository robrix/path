module Path.Package where

import Path.Module

newtype PackageName = PackageName String

data Package = Package
  { packageName    :: PackageName
  , packageTargets :: [Target]
  }

newtype TargetName = TargetName String

data Target
  = Library
    { targetName        :: TargetName
    , targetModuleNames :: [ModuleName]
    , targetConstraints :: [Constraint]
    }

data Constraint
  = Depends PackageName TargetName
