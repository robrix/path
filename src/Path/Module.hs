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
  , moduleImports :: Map.Map ModuleName Span
  , moduleDecls   :: [Decl (Scope Int f a)]
  }
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (Module f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (Module f a)
deriving instance (Show a, forall a . Show a => Show (f a)) => Show (Module f a)

instance Monad f => RModule (Module f) f where
  Module n d p is ds >>=* f = Module n d p is (map (fmap (>>=* f)) ds)

module' :: Applicative f => ModuleName -> Maybe String -> FilePath -> [Spanned ModuleName] -> [Decl (f User)] -> Module f User
module' n d p is ds = Module n d p (Map.fromList (map unSpan is)) (map bind' ds)
  where bind' (Decl u d tm ty) = Decl u d (bind'' <$> tm) (bind'' <$> ty)
          where bind'' = bind (`elemIndex` map declName ds)
        unSpan (i :~ s) = (i, s)

data Decl a = Decl
  { declName :: User
  , declDocs :: Maybe String
  , declTerm :: Spanned a
  , declType :: Spanned a
  }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype ModuleGraph f a = ModuleGraph { unModuleGraph :: Map.Map ModuleName (Module f a) }
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (ModuleGraph f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (ModuleGraph f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (ModuleGraph f a)

instance Monad f => RModule (ModuleGraph f) f where
  ModuleGraph ms >>=* f = ModuleGraph (fmap (>>=* f) ms)

moduleGraph :: [Module f a] -> ModuleGraph f a
moduleGraph = ModuleGraph . Map.fromList . map ((,) . moduleName <*> id)

modules :: ModuleGraph f a -> [Module f a]
modules = Map.elems . unModuleGraph


lookupModule :: (Carrier sig m, Member (Error Doc) sig) => Spanned ModuleName -> ModuleGraph f a -> m (Module f a)
lookupModule i g = maybe (unknownModule i) pure (Map.lookup (unSpanned i) (unModuleGraph g))

cycleFrom :: (Carrier sig m, Effect sig, Member (Error Doc) sig) => ModuleGraph f a -> Spanned ModuleName -> m ()
cycleFrom g m = runReader (Set.empty :: Set.Set ModuleName) (runNonDetOnce (go m)) >>= cyclicImport . fromMaybe (m :| [])
  where go n = do
          notVisited <- asks (Set.notMember (unSpanned n))
          if notVisited then do
            m <- lookupModule n g
            nub . (n <|) <$> local (Set.insert (unSpanned n)) (getAlt (foldMap (Alt . go . uncurry (:~)) (Map.toList (moduleImports m))))
          else
            pure (n :| [])


loadOrder :: (Carrier sig m, Effect sig, Member (Error Doc) sig) => ModuleGraph f a -> m [Module f a]
loadOrder g = reverse <$> execState [] (evalState (Set.empty :: Set.Set ModuleName) (runReader (Set.empty :: Set.Set ModuleName) (for_ (modules g) loopM)))
  where loopM m = do
          visited <- gets (Set.member (moduleName m))
          unless visited . local (Set.insert (moduleName m)) $ do
            for_ (Map.toList (moduleImports m)) (uncurry loop)
            modify (Set.insert (moduleName m))
            modify (m :)
        loop n s = do
          inPath <- asks (Set.member n)
          when inPath (cycleFrom g (n :~ s))
          visited <- gets (Set.member n)
          unless visited . local (Set.insert n) $ do
            m <- lookupModule (n :~ s) g
            for_ (Map.toList (moduleImports m)) (uncurry loop)
            modify (Set.insert n)
            modify (m :)


unknownModule :: (Carrier sig m, Member (Error Doc) sig) => Spanned ModuleName -> m a
unknownModule (name :~ span) = throwError (prettyErr span (pretty "Could not find module" <+> squotes (pretty name)) [])

cyclicImport :: (Carrier sig m, Member (Error Doc) sig) => NonEmpty (Spanned ModuleName) -> m a
cyclicImport (name :~ span :| [])    = throwError (prettyErr span (pretty "Cyclic import of" <+> squotes (pretty name)) [])
cyclicImport (name :~ span :| names) = throwError (vsep
  ( prettyErr span (pretty "Cyclic import of" <+> squotes (pretty name) <> colon) []
  : foldr ((:) . whichImports) [ whichImports (name :~ span) ] names))
  where whichImports (name :~ span) = prettyInfo span (pretty "which imports" <+> squotes (pretty name) <> colon) []
