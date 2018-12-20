{-# LANGUAGE KindSignatures #-}
module Path.Meta where

import Path.Name

data Import (f :: (* -> *) -> * -> *) = Import { importModuleName :: ModuleName }
