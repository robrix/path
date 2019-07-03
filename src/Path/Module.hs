{-# LANGUAGE DeriveTraversable, FlexibleContexts, LambdaCase #-}
module Path.Module where

import Control.Effect
import Control.Effect.Cull (runNonDetOnce)
import Control.Effect.Error
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
import Path.Span

data Module a = Module
  { moduleName    :: ModuleName
  , moduleDocs    :: Maybe String
  , modulePath    :: FilePath
  , moduleImports :: [Spanned Import]
  , moduleDecls   :: [Spanned (Decl a)]
  }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype Import = Import { importModuleName :: ModuleName }
  deriving (Eq, Ord, Show)

data Decl a = Decl
  { declDocs :: Maybe String
  , declName :: User
  , declBody :: a
  }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Pretty a => Pretty (Decl a) where
  pretty (Decl docs v a) = case docs of
    Nothing -> pretty v <+> magenta (pretty "=") <+> pretty a
    Just ds -> pretty ds <> hardline <> pretty v <+> magenta (pretty "=") <+> pretty a


newtype ModuleGraph a = ModuleGraph { unModuleGraph :: Map.Map ModuleName (Module a) }
  deriving (Eq, Ord, Show)

moduleGraph :: [Module a] -> ModuleGraph a
moduleGraph = ModuleGraph . Map.fromList . map ((,) . moduleName <*> id)

modules :: ModuleGraph a -> [Module a]
modules = Map.elems . unModuleGraph


lookupModule :: (Carrier sig m, Member (Error Doc) sig) => ModuleGraph a -> Spanned Import -> m (Module a)
lookupModule g i = maybe (unknownModule i) pure (Map.lookup (importModuleName (unSpanned i)) (unModuleGraph g))

cycleFrom :: (Carrier sig m, Effect sig, Member (Error Doc) sig) => ModuleGraph a -> Spanned Import -> m ()
cycleFrom g m = runReader (Set.empty :: Set.Set ModuleName) (runNonDetOnce (go m)) >>= cyclicImport . fromMaybe (m :| [])
  where go n = do
          let name = importModuleName (unSpanned n)
          notVisited <- asks (Set.notMember name)
          if notVisited then do
            m <- lookupModule g n
            nub . (n <|) <$> local (Set.insert name) (getAlt (foldMap (Alt . go) (moduleImports m)))
          else
            pure (n :| [])


loadOrder :: (Carrier sig m, Effect sig, Member (Error Doc) sig) => ModuleGraph a -> m [Module a]
loadOrder g = reverse <$> execState [] (evalState (Set.empty :: Set.Set ModuleName) (runReader (Set.empty :: Set.Set ModuleName) (for_ (Map.elems (unModuleGraph g)) loopM)))
  where loopM m = do
          visited <- gets (Set.member (moduleName m))
          unless visited . local (Set.insert (moduleName m)) $ do
            for_ (moduleImports m) loop
            modify (Set.insert (moduleName m))
            modify (m :)
        loop n = do
          let i = importModuleName (unSpanned n)
          inPath <- asks (Set.member i)
          when inPath (cycleFrom g n)
          visited <- gets (Set.member i)
          unless visited . local (Set.insert i) $ do
            m <- lookupModule g n
            for_ (moduleImports m) loop
            modify (Set.insert i)
            modify (m :)


unknownModule :: (Carrier sig m, Member (Error Doc) sig) => Spanned Import -> m a
unknownModule (Import name :~ span) = throwError (prettyErr span (pretty "Could not find module" <+> squotes (pretty name)) [])

cyclicImport :: (Carrier sig m, Member (Error Doc) sig) => NonEmpty (Spanned Import) -> m a
cyclicImport (Import name :~ span :| [])    = throwError (prettyErr span (pretty "Cyclic import of" <+> squotes (pretty name)) [])
cyclicImport (Import name :~ span :| names) = throwError (vsep
  ( prettyErr span (pretty "Cyclic import of" <+> squotes (pretty name) <> colon) []
  : foldr ((:) . whichImports) [ whichImports (Import name :~ span) ] names))
  where whichImports (Import name :~ span) = prettyInfo span (pretty "which imports" <+> squotes (pretty name) <> colon) []
