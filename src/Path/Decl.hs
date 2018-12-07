module Path.Decl where

import Data.List.NonEmpty
import qualified Data.Map as Map
import Data.Monoid (First(..))
import qualified Data.Set as Set
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

cycleFrom :: ModuleName -> ModuleGraph -> Maybe [ModuleName]
cycleFrom m g = go Set.empty m
  where go v n
          | n `Set.member` v = Just [n]
          | otherwise        = do
            m <- lookupModule n g
            (n :) <$> getFirst (foldMap (First . go (Set.insert (moduleName m) v) . importModuleName) (moduleImports m))

data ModuleError
  = UnknownModule ModuleName
  | CyclicImport [ModuleName]
  deriving (Eq, Ord, Show)
