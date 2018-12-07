module Path.Package where

import Path.Module

data Package = Package
  { packageName    :: String
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
