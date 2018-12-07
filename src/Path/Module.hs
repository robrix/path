{-# LANGUAGE FlexibleContexts #-}
module Path.Module where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.NonDet
import Control.Effect.Reader
import Control.Effect.State
import Control.Monad (when)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Monoid (Alt(..))
import qualified Data.Set as Set
import Data.Traversable (for)
import Path.Decl

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

lookupModule :: (Carrier sig m, Member (Error ModuleError) sig, Member (Reader ModuleGraph) sig, Monad m) => ModuleName -> m Module
lookupModule name = ask >>= maybe (throwError (UnknownModule name)) ret . Map.lookup name . unModuleGraph

cycleFrom :: (Carrier sig m, Effect sig, Member (Error ModuleError) sig, Member (Reader ModuleGraph) sig, Monad m) => ModuleName -> m ()
cycleFrom m = runReader (Set.empty :: Set.Set ModuleName) (runNonDetOnce (go m)) >>= throwError . CyclicImport . fromMaybe []
  where go n = do
          inPath <- asks (Set.member n)
          if inPath then do
            m <- lookupModule n
            (n :) <$> local (Set.insert (moduleName m)) (getAlt (foldMap (Alt . go . importModuleName) (moduleImports m)))
          else
            pure [n]

data ModuleError
  = UnknownModule ModuleName
  | CyclicImport [ModuleName]
  deriving (Eq, Ord, Show)


loadOrder :: ModuleGraph -> Either ModuleError [Module]
loadOrder g = concat <$> run (runError (evalState (Set.empty :: Set.Set ModuleName) (runReader g (runReader (Set.empty :: Set.Set ModuleName) (for (Map.keys (unModuleGraph g)) loop)))))
  where loop n = do
          inPath <- asks (Set.member n)
          when inPath (cycleFrom n)
          visited <- gets (Set.member n)
          if visited then
            pure []
          else
            local (Set.insert n) $ do
              m <- lookupModule n
              ms <- for (moduleImports m) (loop . importModuleName)
              modify (Set.insert n)
              pure (m : concat ms)