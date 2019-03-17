{-# LANGUAGE FlexibleContexts, LambdaCase, TupleSections #-}
module Path.Renamer where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader hiding (Local)
import Control.Effect.State
import Data.Foldable (toList)
import Data.List.NonEmpty as NonEmpty (NonEmpty(..), filter, nonEmpty, nub)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Path.Core as Core
import Path.Module
import Path.Name
import Path.Plicity
import Path.Pretty
import qualified Path.Surface as Surface
import Path.Usage
import Prelude hiding (pi)
import Text.Trifecta.Rendering (Span)

resolveTerm :: (Carrier sig m, Member (Error ResolveError) sig, Member Naming sig, Member (Reader Mode) sig, Member (Reader ModuleName) sig, Member (Reader Resolution) sig, Member (Reader Span) sig)
            => Surface.Surface
            -> m Core
resolveTerm = \case
  Surface.Var v -> Var <$> resolveName v
  Surface.Lam (Just v) b -> do
    res <- asks (lookupName v)
    let v' = case res of
          Just (Local (User v'):|[]) -> prime v'
          _ -> v
    local (insertLocal v v') (Lam (Just v') <$> resolveTerm b)
  Surface.Lam _ b -> Lam Nothing <$> resolveTerm b
  f Surface.:$ a -> (:$) <$> resolveTerm f <*> resolveTerm a
  Surface.Type -> pure Type
  Surface.Pi (Just v) ie u t b -> do
    res <- asks (lookupName v)
    let v' = case res of
          Just (Local (User v'):|[]) -> prime v'
          _ -> v
    Pi (Just v') ie u <$> resolveTerm t <*> local (insertLocal v v') (resolveTerm b)
  Surface.Pi _ ie u t b -> Pi Nothing ie u <$> resolveTerm t <*> resolveTerm b
  (u, a) Surface.:-> b -> Pi Nothing Ex u <$> resolveTerm a <*> resolveTerm b
  Surface.Hole v -> pure (Hole v)
  Surface.Ann ann a -> Ann ann <$> local (const ann) (resolveTerm a)
  where prime (Id s) = Id (s <> "ʹ")
        prime (Op o) = Op o


data Mode = Decl | Defn
  deriving (Eq, Ord, Show)

resolveDecl :: (Carrier sig m, Member (Error ResolveError) sig, Member Naming sig, Member (Reader ModuleName) sig, Member (Reader Span) sig, Member (State Resolution) sig) => Decl User Surface.Surface -> m (Decl Qualified Core)
resolveDecl = \case
  Declare n ty span -> do
    res <- get
    moduleName <- ask
    ty' <- runReader (res :: Resolution) (runReader Decl (resolveTerm (generalize res ty)))
    Declare (moduleName :.: n) ty' span <$ modify (insertGlobal n moduleName)
    where generalize res ty = foldr bind ty (fvs ty Set.\\ Map.keysSet (unResolution res))
          bind n = Surface.Pi (Just n) Im Zero Surface.Type -- FIXME: insert metavariables for the type
  Define n tm span -> do
    res <- get
    moduleName <- ask
    tm' <- runReader (res :: Resolution) (runReader Defn (resolveTerm tm))
    Define (moduleName :.: n) tm' span <$ modify (insertGlobal n moduleName)
  Doc t d span -> Doc t <$> resolveDecl d <*> pure span

resolveModule :: (Carrier sig m, Effect sig, Member (Error ResolveError) sig, Member Naming sig, Member (Reader Span) sig, Member (State Resolution) sig) => Module User Surface.Surface -> m (Module Qualified Core)
resolveModule m = do
  res <- get
  (res, decls) <- runState (filterResolution amongImports res) (runReader (moduleName m) (traverse resolveDecl (moduleDecls m)))
  modify (<> res)
  pure (m { moduleDecls = decls })
  where amongImports q = any (flip inModule q . importModuleName) (moduleImports m)

newtype Resolution = Resolution { unResolution :: Map.Map User (NonEmpty (Name Local)) }
  deriving (Eq, Ord, Show)

instance Semigroup Resolution where
  Resolution m1 <> Resolution m2 = Resolution (Map.unionWith (fmap nub . (<>)) m1 m2)

insertLocal :: User -> User -> Resolution -> Resolution
insertLocal n n' = Resolution . Map.insert n (Local (User n'):|[]) . unResolution

insertGlobal :: User -> ModuleName -> Resolution -> Resolution
insertGlobal n m = Resolution . Map.insertWith (fmap nub . (<>)) n (Global (m:.:n):|[]) . unResolution

lookupName :: User -> Resolution -> Maybe (NonEmpty (Name Local))
lookupName n = Map.lookup n . unResolution

resolveName :: (Carrier sig m, Member (Error ResolveError) sig, Member Naming sig, Member (Reader Mode) sig, Member (Reader Resolution) sig, Member (Reader Span) sig) => User -> m (Name Local)
resolveName v = do
  res <- asks (lookupName v)
  mode <- ask
  s <- ask
  res <- case mode of
    Decl -> maybe (gensym "" >>= \ n -> pure (Local (Gen n) :| [])) pure res
    Defn -> maybe (throwError (FreeVariable v s)) pure res
  unambiguous v s res

filterResolution :: (Name Local -> Bool) -> Resolution -> Resolution
filterResolution f = Resolution . Map.mapMaybe matches . unResolution
  where matches = nonEmpty . NonEmpty.filter f

unambiguous :: (Carrier sig m, Member (Error ResolveError) sig) => User -> Span -> NonEmpty (Name Local) -> m (Name Local)
unambiguous _ _ (q:|[]) = pure q
unambiguous v s (q:|qs) = throwError (AmbiguousName v s (q :| qs))


data ResolveError
  = FreeVariable User Span
  | AmbiguousName User Span (NonEmpty (Name Local))

instance Pretty ResolveError where
  pretty = \case
    FreeVariable name span -> prettyErr span (pretty "free variable" <+> squotes (pretty name)) []
    AmbiguousName name span sources -> prettyErr span (pretty "ambiguous name" <+> squotes (pretty name)) [nest 2 (vsep
      ( pretty "it could refer to"
      : map prettyQName (toList sources)))]

instance PrettyPrec ResolveError
