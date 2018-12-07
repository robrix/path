module Path.Package where

import Path.Module

newtype PackageName = PackageName String

data Package = Package
  { packageName    :: PackageName
  , packageTargets :: [Target]
  }

data Target
  = Library
    { targetName        :: String
    , targetModuleNames :: [ModuleName]
    }
  | Executable
    { targetName        :: String
    , targetModuleNames :: [ModuleName]
    }
  | Test
    { targetName        :: String
    , targetModuleNames :: [ModuleName]
    }
