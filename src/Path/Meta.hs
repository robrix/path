{-# LANGUAGE KindSignatures #-}
module Path.Meta where

import Path.Name

data Module v f = Module
  { moduleName    :: ModuleName
  , moduleImports :: [f Import]
  }

data Import (f :: (* -> *) -> * -> *) = Import { importModuleName :: ModuleName }
