{-# LANGUAGE FlexibleContexts #-}
module Path.Module where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.NonDet (runNonDetOnce)
import Control.Effect.Reader
import Control.Effect.State
import Control.Monad (unless, when)
import Data.Foldable (for_)
import Data.List.NonEmpty (NonEmpty(..), (<|))
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Monoid (Alt(..))
import qualified Data.Set as Set
import Path.Decl
import Path.Name
import Path.Pretty
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import Text.Trifecta.Rendering (Span)

data Module v a ann = Module
  { moduleName    :: ModuleName
  , modulePath    :: FilePath
  , moduleImports :: [Import ann]
  , moduleDecls   :: [Decl v a]
  }
  deriving (Eq, Ord, Show)

data Import ann = Import { importModuleName :: ModuleName, importAnn :: ann }
  deriving (Eq, Ord, Show)


newtype ModuleGraph v a ann = ModuleGraph { unModuleGraph :: Map.Map ModuleName (Module v a ann) }
  deriving (Eq, Ord, Show)

moduleGraph :: [Module v a ann] -> ModuleGraph v a ann
moduleGraph = ModuleGraph . Map.fromList . map ((,) . moduleName <*> id)

modules :: ModuleGraph v a ann -> [Module v a ann]
modules = Map.elems . unModuleGraph

lookupModule :: (Carrier sig m, Member (Error ModuleError) sig) => ModuleGraph v a Span -> ModuleName -> m (Module v a Span)
lookupModule g name = maybe (throwError (UnknownModule name)) ret (Map.lookup name (unModuleGraph g))

cycleFrom :: (Carrier sig m, Effect sig, Member (Error ModuleError) sig, Monad m) => ModuleGraph v a Span -> ModuleName -> m ()
cycleFrom g m = runReader (Set.empty :: Set.Set ModuleName) (runNonDetOnce (go m)) >>= throwError . CyclicImport . fromMaybe (m :| [])
  where go n = do
          inPath <- asks (Set.member n)
          if inPath then do
            m <- lookupModule g n
            (n <|) <$> local (Set.insert (moduleName m)) (getAlt (foldMap (Alt . go . importModuleName) (moduleImports m)))
          else
            pure (n :| [])

data ModuleError
  = UnknownModule ModuleName
  | CyclicImport (NonEmpty ModuleName)
  deriving (Eq, Ord, Show)

instance Pretty ModuleError where
  pretty (UnknownModule name) = hsep (map pretty (words "Could not find module") <> [squotes (pretty name)])
  pretty (CyclicImport (name :| [])) = nest 2 (vsep
    [ hsep (map pretty (words "Module imports form a cycle:"))
    , hsep [ pretty "module", squotes (pretty name), pretty "imports", pretty "itself" ]
    ])
  pretty (CyclicImport (name :| name' : names)) = nest 2 (vsep
    ( hsep (map pretty (words "Module imports form a cycle:"))
    : hsep [ pretty "       module", squotes (pretty name) ]
    : hsep [ pretty "      imports", squotes (pretty name') ]
    : foldr ((:) . whichImports) [ whichImports name ] names
    ))
    where whichImports name = fillSep [ pretty "which imports", squotes (pretty name) ]

instance PrettyPrec ModuleError


loadOrder :: (Carrier sig m, Effect sig, Member (Error ModuleError) sig, Monad m) => ModuleGraph v a Span -> m [Module v a Span]
loadOrder g = reverse <$> execState [] (evalState (Set.empty :: Set.Set ModuleName) (runReader (Set.empty :: Set.Set ModuleName) (for_ (Map.keys (unModuleGraph g)) loop)))
  where loop n = do
          inPath <- asks (Set.member n)
          when inPath (cycleFrom g n)
          visited <- gets (Set.member n)
          unless visited . local (Set.insert n) $ do
            m <- lookupModule g n
            for_ (moduleImports m) (loop . importModuleName)
            modify (Set.insert n)
            modify (m :)
