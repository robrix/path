module Path.Decl where

import Data.List.NonEmpty
import qualified Data.Map as Map
import Path.Surface
import Path.Term

data Decl
  = Declare String (Term Surface)
  | Define String (Term Surface)
  deriving (Eq, Ord, Show)

type ModuleName = NonEmpty String

data Module = Module
  { moduleName    :: ModuleName
  , moduleImports :: [Import]
  , moduleDecls   :: [Decl]
  }
  deriving (Eq, Ord, Show)

newtype Import = Import { importModuleName :: ModuleName }
  deriving (Eq, Ord, Show)


newtype ModuleGraph = ModuleGraph { unModuleGraph :: Map.Map ModuleName Module }
  deriving (Eq, Ord, Show)

moduleGraph :: [Module] -> ModuleGraph
moduleGraph = ModuleGraph . Map.fromList . map ((,) . moduleName <*> id)

lookupModule :: ModuleName -> ModuleGraph -> Maybe Module
lookupModule name = Map.lookup name . unModuleGraph
