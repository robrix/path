{-# LANGUAGE DeriveTraversable, FlexibleContexts, LambdaCase #-}
module Path.Module where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.NonDet (runNonDetOnce)
import Control.Effect.Reader
import Control.Effect.State
import Control.Monad (unless, when)
import Data.Foldable (for_)
import Data.List.NonEmpty (NonEmpty(..), (<|), nub)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Monoid (Alt(..))
import qualified Data.Set as Set
import Path.Name
import Path.Pretty
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import Text.Trifecta.Rendering (Span)

data Module v a = Module
  { moduleName    :: ModuleName
  , moduleDocs    :: Maybe String
  , modulePath    :: FilePath
  , moduleImports :: [Import]
  , moduleDecls   :: [Decl v a]
  }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Import = Import { importModuleName :: ModuleName, importAnn :: Span }
  deriving (Eq, Ord, Show)

data Decl v a
  = Declare v a
  | Define v a
  | Doc String (Decl v a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)


newtype ModuleGraph v a = ModuleGraph { unModuleGraph :: Map.Map ModuleName (Module v a) }
  deriving (Eq, Ord, Show)

moduleGraph :: [Module v a] -> ModuleGraph v a
moduleGraph = ModuleGraph . Map.fromList . map ((,) . moduleName <*> id)

modules :: ModuleGraph v a -> [Module v a]
modules = Map.elems . unModuleGraph

lookupModule :: (Carrier sig m, Member (Error ModuleError) sig) => ModuleGraph v a -> Import -> m (Module v a)
lookupModule g i = maybe (throwError (UnknownModule i)) ret (Map.lookup (importModuleName i) (unModuleGraph g))

cycleFrom :: (Carrier sig m, Effect sig, Member (Error ModuleError) sig, Monad m) => ModuleGraph v a -> Import -> m ()
cycleFrom g m = runReader (Set.empty :: Set.Set ModuleName) (runNonDetOnce (go m)) >>= throwError . CyclicImport . fromMaybe (m :| [])
  where go n = do
          notVisited <- asks (Set.notMember (importModuleName n))
          if notVisited then do
            m <- lookupModule g n
            nub . (n <|) <$> local (Set.insert (importModuleName n)) (getAlt (foldMap (Alt . go) (moduleImports m)))
          else
            pure (n :| [])

data ModuleError
  = UnknownModule Import
  | CyclicImport (NonEmpty Import)
  deriving (Eq, Ord, Show)

instance Pretty ModuleError where
  pretty = \case
    UnknownModule (Import name span) -> prettyErr span (pretty "Could not find module" <+> squotes (pretty name)) Nothing
    CyclicImport (Import name span :| []) -> prettyErr span (pretty "Cyclic import of" <+> squotes (pretty name)) Nothing
    CyclicImport (Import name span :| names) -> vsep
      ( prettyErr span (pretty "Cyclic import of" <+> squotes (pretty name) <> colon) Nothing
      : foldr ((:) . whichImports) [ whichImports (Import name span) ] names)
    where whichImports (Import name span) = prettyInfo span (pretty "which imports" <+> squotes (pretty name) <> colon) Nothing

instance PrettyPrec ModuleError


loadOrder :: (Carrier sig m, Effect sig, Member (Error ModuleError) sig, Monad m) => ModuleGraph v a -> m [Module v a]
loadOrder g = reverse <$> execState [] (evalState (Set.empty :: Set.Set ModuleName) (runReader (Set.empty :: Set.Set ModuleName) (for_ (Map.elems (unModuleGraph g)) loopM)))
  where loopM m = do
          visited <- gets (Set.member (moduleName m))
          unless visited . local (Set.insert (moduleName m)) $ do
            for_ (moduleImports m) loop
            modify (Set.insert (moduleName m))
            modify (m :)
        loop n = do
          inPath <- asks (Set.member (importModuleName n))
          when inPath (cycleFrom g n)
          visited <- gets (Set.member (importModuleName n))
          unless visited . local (Set.insert (importModuleName n)) $ do
            m <- lookupModule g n
            for_ (moduleImports m) loop
            modify (Set.insert (importModuleName n))
            modify (m :)
