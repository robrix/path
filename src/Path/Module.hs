{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, StandaloneDeriving, TypeOperators #-}
module Path.Module where

import Control.Effect
import Control.Effect.Cull (runNonDetOnce)
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
import Data.Void
import Path.Error
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

newtype ModuleGraph f a = ModuleGraph { unModuleGraph :: Map.Map ModuleName (ScopeH Qualified (Module f) f a) }
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (ModuleGraph f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (ModuleGraph f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (ModuleGraph f a)

instance Monad f => RModule (ModuleGraph f) f where
  ModuleGraph ms >>=* f = ModuleGraph (fmap (>>=* f) ms)

moduleGraph :: Applicative f => [Module f Qualified] -> ModuleGraph f Void
moduleGraph ms = ModuleGraph (Map.fromList (map ((,) .moduleName <*> bindHEither Left) ms))

rename :: (Carrier sig m, Foldable t, Member (Error Doc) sig, Member (Reader Span) sig)
       => t (Module f a)
       -> User
       -> m Qualified
rename ms n = case foldMap (\ m -> [ moduleName m :.: n | d <- moduleDecls m, declName d == n ]) ms of
  [x]  -> pure x
  []   -> freeVariable n
  x:xs -> ambiguousName n (x:|xs)

runDecl :: Carrier sig m => (a -> ReaderC Span m b) -> Decl a -> m (Decl b)
runDecl f (Decl n d tm ty) = do
  tm' <- runSpanned f tm
  ty' <- runSpanned f ty
  pure (Decl n d tm' ty')

renameDecl :: (Carrier sig m, Foldable t, Member (Error Doc) sig, Traversable g)
           => t (Module f a)
           -> Decl (g User)
           -> m (Decl (g Qualified))
renameDecl ms = runDecl (traverse (rename ms))

renameModuleGraph :: (Applicative f, Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig, Traversable f) => [Module f User] -> m (ModuleGraph f Void)
renameModuleGraph ms = do
  ms' <- traverse (\ m -> traverse (rename (imported m)) m) ms
  pure (ModuleGraph (Map.fromList (map ((,) . moduleName <*> bindHEither Left) ms')))
  where imported m = filter (flip Set.member imports . moduleName) ms
          where imports = Map.keysSet (moduleImports m)

modules :: Monad f => ModuleGraph f Void -> [Module f Qualified]
modules (ModuleGraph m) = map (instantiateHEither (either pure absurd)) (Map.elems m)


lookupModule :: (Carrier sig m, Member (Error Doc) sig) => Spanned ModuleName -> ModuleGraph f a -> m (ScopeH Qualified (Module f) f a)
lookupModule i g = maybe (unknownModule i) pure (Map.lookup (unSpanned i) (unModuleGraph g))

cycleFrom :: (Carrier sig m, Effect sig, Member (Error Doc) sig) => ModuleGraph f a -> Spanned ModuleName -> m ()
cycleFrom g m = runReader (Set.empty :: Set.Set ModuleName) (runNonDetOnce (go m)) >>= cyclicImport . fromMaybe (m :| [])
  where go n = do
          notVisited <- asks (Set.notMember (unSpanned n))
          if notVisited then do
            m <- lookupModule n g
            nub . (n <|) <$> local (Set.insert (unSpanned n)) (getAlt (foldMap (Alt . go . uncurry (:~)) (Map.toList (moduleImports (unScopeH m)))))
          else
            pure (n :| [])


loadOrder :: (Carrier sig m, Effect sig, Member (Error Doc) sig) => ModuleGraph f Void -> m [ScopeH Qualified (Module f) f Void]
loadOrder g = reverse <$> execState [] (evalState (Set.empty :: Set.Set ModuleName) (runReader (Set.empty :: Set.Set ModuleName) (for_ (unModuleGraph g) loopM)))
  where loopM m = do
          visited <- gets (Set.member (moduleName (unScopeH m)))
          unless visited . local (Set.insert (moduleName (unScopeH m))) $ do
            for_ (Map.toList (moduleImports (unScopeH m))) (uncurry loop)
            modify (Set.insert (moduleName (unScopeH m)))
            modify (m :)
        loop n s = do
          inPath <- asks (Set.member n)
          when inPath (cycleFrom g (n :~ s))
          visited <- gets (Set.member n)
          unless visited . local (Set.insert n) $ do
            m <- lookupModule (n :~ s) g
            for_ (Map.toList (moduleImports (unScopeH m))) (uncurry loop)
            modify (Set.insert n)
            modify (m :)
