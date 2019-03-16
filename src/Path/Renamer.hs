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
            -> m (Core (Name Gensym))
resolveTerm = \case
  Surface.Var v -> pure <$> resolveName v
  Surface.Lam v b -> do
    n <- gensym ""
    local (insertLocal v n) (lam (Local n) <$> resolveTerm b)
  f Surface.:$ a -> (:$) <$> resolveTerm f <*> resolveTerm a
  Surface.Type -> pure Type
  Surface.Pi v ie u t b -> do
    n <- gensym ""
    pi . ((Local n, ie, u) :::) <$> resolveTerm t <*> local (insertLocal v n) (resolveTerm b)
  (u, a) Surface.:-> b ->
    pi <$> ((:::) . (, Ex, u) . Local <$> gensym "" <*> resolveTerm a) <*> resolveTerm b
  Surface.Hole v -> Hole . Global . (:.: v) <$> ask
  Surface.Ann ann a -> Ann ann <$> local (const ann) (resolveTerm a)

data Mode = Decl | Defn
  deriving (Eq, Ord, Show)

resolveDecl :: (Carrier sig m, Member (Error ResolveError) sig, Member Naming sig, Member (Reader ModuleName) sig, Member (Reader Span) sig, Member (State Resolution) sig) => Decl User Surface.Surface -> m (Decl Qualified (Core (Name Gensym)))
resolveDecl = \case
  Declare n ty -> do
    res <- get
    moduleName <- ask
    ty' <- runReader (res :: Resolution) (runReader Decl (resolveTerm (generalize res ty)))
    Declare (moduleName :.: n) ty' <$ modify (insertGlobal n moduleName)
    where generalize res ty = foldr bind ty (fvs ty Set.\\ Map.keysSet (unResolution res))
          bind n = Surface.Pi (Just n) Im Zero Surface.Type -- FIXME: insert metavariables for the type
  Define n tm -> do
    res <- get
    moduleName <- ask
    tm' <- runReader (res :: Resolution) (runReader Defn (resolveTerm tm))
    Define (moduleName :.: n) tm' <$ modify (insertGlobal n moduleName)
  Doc t d -> Doc t <$> resolveDecl d

resolveModule :: (Carrier sig m, Effect sig, Member (Error ResolveError) sig, Member Naming sig, Member (Reader Span) sig, Member (State Resolution) sig) => Module User Surface.Surface -> m (Module Qualified (Core (Name Gensym)))
resolveModule m = do
  res <- get
  (res, decls) <- runState (filterResolution amongImports res) (runReader (moduleName m) (traverse resolveDecl (moduleDecls m)))
  modify (<> res)
  pure (m { moduleDecls = decls })
  where amongImports q = any (flip inModule q . importModuleName) (moduleImports m)

newtype Resolution = Resolution { unResolution :: Map.Map User (NonEmpty (Name Gensym)) }
  deriving (Eq, Ord, Show)

instance Semigroup Resolution where
  Resolution m1 <> Resolution m2 = Resolution (Map.unionWith (fmap nub . (<>)) m1 m2)

insertLocal :: Maybe User -> Gensym -> Resolution -> Resolution
insertLocal Nothing  _ = id
insertLocal (Just n) m = Resolution . Map.insert n (Local m:|[]) . unResolution

insertGlobal :: User -> ModuleName -> Resolution -> Resolution
insertGlobal n m = Resolution . Map.insertWith (fmap nub . (<>)) n (Global (m:.:n):|[]) . unResolution

lookupName :: User -> Resolution -> Maybe (NonEmpty (Name Gensym))
lookupName n = Map.lookup n . unResolution

resolveName :: (Carrier sig m, Member (Error ResolveError) sig, Member Naming sig, Member (Reader Mode) sig, Member (Reader Resolution) sig, Member (Reader Span) sig) => User -> m (Name Gensym)
resolveName v = do
  res <- asks (lookupName v)
  mode <- ask
  s <- ask
  n <- gensym ""
  case mode of
    Decl -> maybe (pure (Local n :| [])) pure res >>= unambiguous v s
    Defn -> maybe (throwError (FreeVariable v s)) pure res >>= unambiguous v s

filterResolution :: (Name Gensym -> Bool) -> Resolution -> Resolution
filterResolution f = Resolution . Map.mapMaybe matches . unResolution
  where matches = nonEmpty . NonEmpty.filter f

unambiguous :: (Carrier sig m, Member (Error ResolveError) sig) => User -> Span -> NonEmpty (Name Gensym) -> m (Name Gensym)
unambiguous _ _ (q:|[]) = pure q
unambiguous v s (q:|qs) = throwError (AmbiguousName v s (q :| qs))


data ResolveError
  = FreeVariable User Span
  | AmbiguousName User Span (NonEmpty (Name Gensym))

instance Pretty ResolveError where
  pretty = \case
    FreeVariable name span -> prettyErr span (pretty "free variable" <+> squotes (pretty name)) []
    AmbiguousName name span sources -> prettyErr span (pretty "ambiguous name" <+> squotes (pretty name)) [nest 2 (vsep
      ( pretty "it could refer to"
      : map prettyQName (toList sources)))]

instance PrettyPrec ResolveError
