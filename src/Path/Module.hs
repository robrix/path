{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, StandaloneDeriving, TypeOperators #-}
module Path.Module where

import Control.Effect
import Control.Effect.Cull (runNonDetOnce)
import Control.Effect.Error
import Control.Effect.Reader
import Control.Effect.State
import Control.Monad (unless, when)
import Control.Monad.Module
import Data.Foldable (for_)
import Data.List.NonEmpty (NonEmpty(..), (<|), nub)
import Data.List (elemIndex)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Monoid (Alt(..))
import qualified Data.Set as Set
import Path.Name
import Path.Pretty
import Path.Scope
import Path.Span

data Module f a = Module
  { moduleName    :: ModuleName
  , moduleDocs    :: Maybe String
  , modulePath    :: FilePath
  , moduleImports :: [Spanned Import]
  , moduleDecls   :: [Decl (Scope Int f a)]
  }
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (Module f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (Module f a)
deriving instance (Show a, forall a . Show a => Show (f a)) => Show (Module f a)

instance Monad f => RModule (Module f) f where
  Module n d p is ds >>=* f = Module n d p is (map (fmap (>>=* f)) ds)

module' :: (Applicative f, Eq a) => ModuleName -> Maybe String -> FilePath -> [Spanned Import] -> [(a, Decl (f a))] -> Module f a
module' n d p is ds = Module n d p is (map bind' ds)
  where bind' (_, Decl u d tm ty) = Decl u d (bind'' <$> tm) (bind'' <$> ty)
          where bind'' = bind (`elemIndex` map fst ds)

newtype Import = Import { importModuleName :: ModuleName }
  deriving (Eq, Ord, Show)

data Decl a = Decl
  { declName :: User
  , declDocs :: Maybe String
  , declTerm :: Spanned a
  , declType :: Spanned a
  }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype ModuleGraph f a = ModuleGraph { unModuleGraph :: Map.Map ModuleName (Module f a) }

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (ModuleGraph f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (ModuleGraph f a)
deriving instance (Show a, forall a . Show a => Show (f a)) => Show (ModuleGraph f a)

moduleGraph :: [Module f a] -> ModuleGraph f a
moduleGraph = ModuleGraph . Map.fromList . map ((,) . moduleName <*> id)

modules :: ModuleGraph f a -> [Module f a]
modules = Map.elems . unModuleGraph


lookupModule :: (Carrier sig m, Member (Error Doc) sig) => ModuleGraph f a -> Spanned Import -> m (Module f a)
lookupModule g i = maybe (unknownModule i) pure (Map.lookup (importModuleName (unSpanned i)) (unModuleGraph g))

cycleFrom :: (Carrier sig m, Effect sig, Member (Error Doc) sig) => ModuleGraph f a -> Spanned Import -> m ()
cycleFrom g m = runReader (Set.empty :: Set.Set ModuleName) (runNonDetOnce (go m)) >>= cyclicImport . fromMaybe (m :| [])
  where go n = do
          let name = importModuleName (unSpanned n)
          notVisited <- asks (Set.notMember name)
          if notVisited then do
            m <- lookupModule g n
            nub . (n <|) <$> local (Set.insert name) (getAlt (foldMap (Alt . go) (moduleImports m)))
          else
            pure (n :| [])


loadOrder :: (Carrier sig m, Effect sig, Member (Error Doc) sig) => ModuleGraph f a -> m [Module f a]
loadOrder g = reverse <$> execState [] (evalState (Set.empty :: Set.Set ModuleName) (runReader (Set.empty :: Set.Set ModuleName) (for_ (modules g) loopM)))
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
