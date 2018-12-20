module Path.Meta where

import Path.Name

data Module v t f = Module
  { moduleName    :: ModuleName
  , moduleImports :: [f Import]
  , moduleDecls   :: [f (Decl v t)]
  }

data Import = Import { importModuleName :: ModuleName }

data Decl v t
  = Decl v t
  | Defn v t
