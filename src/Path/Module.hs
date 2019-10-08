{-# LANGUAGE DeriveGeneric, DeriveTraversable, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, StandaloneDeriving, TypeOperators #-}
module Path.Module where

import Control.Effect.Carrier
import Control.Effect.Cull (runNonDetOnce)
import Control.Effect.Error
import Control.Effect.Reader
import Control.Effect.State
import Control.Monad (unless, when)
import Data.Foldable (for_, toList)
import Data.List.NonEmpty (NonEmpty(..), (<|), nub)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Monoid (Alt(..))
import qualified Data.Set as Set
import Data.Void
import GHC.Generics (Generic1)
import Path.Error
import Path.Name
import Path.Span
import Syntax.Module
import Syntax.Scope
import Syntax.Trans.Scope
import Syntax.Var hiding (fromMaybe)

data Module f a = Module
  { moduleName    :: ModuleName
  , moduleDocs    :: Maybe String
  , modulePath    :: FilePath
  , moduleImports :: Map.Map ModuleName Excerpt
  , moduleDecls   :: Map.Map User (Decl (Scope User f a))
  }
  deriving (Foldable, Functor, Generic1, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (Module f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (Module f a)
deriving instance (Show a, forall a . Show a => Show (f a)) => Show (Module f a)

instance HFunctor Module

instance RightModule Module where
  Module n d p is ds >>=* f = Module n d p is (fmap (fmap (>>=* f)) ds)

module' :: Applicative f => ModuleName -> Maybe String -> FilePath -> [Spanned ModuleName] -> [Decl (f User)] -> Module f User
module' n d p is ds = Module n d p (Map.fromList (map unSpan is)) decls
  where abstract' (Decl u d tm ty) = Decl u d (abstract (fmap declName . flip Map.lookup decls) <$> tm) (abstract (fmap declName . flip Map.lookup decls) <$> ty)
        unSpan (i :~ s) = (i, s)
        decls = Map.fromList (map ((,) . declName <*> abstract') ds)

data Decl a = Decl
  { declName :: User
  , declDocs :: Maybe String
  , declTerm :: Spanned a
  , declType :: Spanned a
  }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype ModuleGraph f a = ModuleGraph { unModuleGraph :: Map.Map ModuleName (ScopeT Qualified Module f a) }
  deriving (Foldable, Functor, Monoid, Semigroup, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (ModuleGraph f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (ModuleGraph f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (ModuleGraph f a)

instance HFunctor ModuleGraph where
  hmap f (ModuleGraph graph) = ModuleGraph (ScopeT . hmap f . fmap (fmap f) . unScopeT <$> graph)

instance RightModule ModuleGraph where
  ModuleGraph ms >>=* f = ModuleGraph (fmap (>>=* f) ms)

moduleGraph :: Applicative f => [Module f Qualified] -> ModuleGraph f Void
moduleGraph ms = ModuleGraph (Map.fromList (map ((,) . moduleName <*> abstractVarT B) ms))

restrict :: Set.Set ModuleName -> ModuleGraph f a -> ModuleGraph f a
restrict keys = ModuleGraph . flip Map.restrictKeys keys . unModuleGraph

rename :: (Carrier sig m, Foldable t, Member (Error Notice) sig, Member (Reader Excerpt) sig)
       => t (Module f a)
       -> User
       -> m Qualified
rename ms n = case foldMap (\ m -> [ moduleName m :.: n | d <- toList (moduleDecls m), declName d == n ]) ms of
  [x]  -> pure x
  []   -> freeVariables (pure n)
  x:xs -> ambiguousName n (x:|xs)

runDecl :: Carrier sig m => (a -> ReaderC Excerpt m b) -> Decl a -> m (Decl b)
runDecl f (Decl n d tm ty) = do
  tm' <- runSpanned f tm
  ty' <- runSpanned f ty
  pure (Decl n d tm' ty')

renameDecl :: (Carrier sig m, Foldable t, Member (Error Notice) sig, Traversable g)
           => t (Module f a)
           -> Decl (g User)
           -> m (Decl (g Qualified))
renameDecl ms = runDecl (traverse (rename ms))

renameModule :: (Carrier sig m, Foldable t, Member (Error Notice) sig, Traversable g)
             => t (Module f a)
             -> Module g User
             -> m (Module g Qualified)
renameModule ms m = do
  ds <- traverse (runDecl (traverse (rename ms))) (moduleDecls m)
  pure m { moduleDecls = ds }

renameModuleGraph :: (Applicative f, Carrier sig m, Member (Error Notice) sig, Traversable f) => [Module f User] -> m (ModuleGraph f Void)
renameModuleGraph ms = do
  ms' <- traverse (\ m -> renameModule (imported m) m) ms
  pure (ModuleGraph (Map.fromList (map ((,) . moduleName <*> abstractVarT B) ms')))
  where imported m = filter (flip Set.member imports . moduleName) ms
          where imports = Map.keysSet (moduleImports m)

modules :: Monad f => ModuleGraph f Void -> [Module f Qualified]
modules (ModuleGraph m) = map (instantiateVarT (unVar pure absurd)) (Map.elems m)

lookup :: Monad f => Qualified -> ModuleGraph f Void -> Maybe (Decl (f Qualified))
lookup (mn :.: n) (ModuleGraph g) = do
  sm <- Map.lookup mn g
  let m = instantiateVarT (unVar pure absurd) sm
  decl <- Map.lookup n (moduleDecls m)
  pure (instantiate (pure . (moduleName m :.:)) <$> decl)


lookupModule :: (Carrier sig m, Member (Error Notice) sig) => Spanned ModuleName -> ModuleGraph f a -> m (ScopeT Qualified Module f a)
lookupModule i g = maybe (unknownModule i) pure (Map.lookup (unSpanned i) (unModuleGraph g))

cycleFrom :: (Carrier sig m, Effect sig, Member (Error Notice) sig) => ModuleGraph f a -> Spanned ModuleName -> m ()
cycleFrom g m = runReader (Set.empty :: Set.Set ModuleName) (runNonDetOnce (go m)) >>= cyclicImport . fromMaybe (m :| [])
  where go n = do
          notVisited <- asks (Set.notMember (unSpanned n))
          if notVisited then do
            m <- lookupModule n g
            nub . (n <|) <$> local (Set.insert (unSpanned n)) (getAlt (foldMap (Alt . go . uncurry (:~)) (Map.toList (moduleImports (unScopeT m)))))
          else
            pure (n :| [])


loadOrder :: (Carrier sig m, Effect sig, Member (Error Notice) sig) => ModuleGraph f Void -> m [ScopeT Qualified Module f Void]
loadOrder g = reverse <$> execState [] (evalState (Set.empty :: Set.Set ModuleName) (runReader (Set.empty :: Set.Set ModuleName) (for_ (unModuleGraph g) loopM)))
  where loopM m = do
          visited <- gets (Set.member (moduleName (unScopeT m)))
          unless visited . local (Set.insert (moduleName (unScopeT m))) $ do
            for_ (Map.toList (moduleImports (unScopeT m))) (uncurry loop)
            modify (Set.insert (moduleName (unScopeT m)))
            modify (m :)
        loop n s = do
          inPath <- asks (Set.member n)
          when inPath (cycleFrom g (n :~ s))
          visited <- gets (Set.member n)
          unless visited . local (Set.insert n) $ do
            m <- lookupModule (n :~ s) g
            for_ (Map.toList (moduleImports (unScopeT m))) (uncurry loop)
            modify (Set.insert n)
            modify (m :)
