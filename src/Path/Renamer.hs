{-# LANGUAGE FlexibleContexts, LambdaCase, TupleSections #-}
module Path.Renamer where

import Control.Effect
import Control.Effect.Reader hiding (Local)
import Control.Effect.State
import Data.List.NonEmpty as NonEmpty (NonEmpty(..), filter, nonEmpty, nub)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Path.Core as Core
import Path.Error
import Path.Module
import Path.Name
import Path.Plicity
import Path.Pretty
import qualified Path.Surface as Surface
import Path.Usage
import Prelude hiding (pi)
import Text.Trifecta.Rendering (Span, Spanned(..))

resolveTerm :: (Carrier sig m, Member (Error Doc) sig, Member Naming sig, Member (Reader Mode) sig, Member (Reader ModuleName) sig, Member (Reader Resolution) sig, Member (Reader Span) sig)
            => Surface.Surface
            -> m (Core Name)
resolveTerm = \case
  Surface.Var v -> Var <$> resolveName v
  Surface.Lam v b -> do
    v' <- gensym (maybe "lam" show v)
    local (insertLocal v v') (Lam (Ex :< v) . bind (Local v') <$> resolveTerm b)
  f Surface.:$ a -> (:$) <$> resolveTerm f <*> resolveTerm a
  Surface.Type -> pure Type
  Surface.Pi (ie :< (v, u, t)) b -> do
    v' <- gensym (maybe "lam" show v)
    Pi . (ie :<) . (v, u,) <$> resolveTerm t <*> local (insertLocal v v') (bind (Local v') <$> resolveTerm b)
  (u, a) Surface.:-> b -> do
    v <- gensym "pi"
    Pi . (Ex :<) . (Nothing, u,) <$> resolveTerm a <*> (bind (Local v) <$> resolveTerm b)
  Surface.Hole v -> Hole <$> resolveName v
  Surface.Ann ann a -> Ann ann <$> local (const ann) (resolveTerm a)


data Mode = Decl | Defn
  deriving (Eq, Ord, Show)

resolveDecl :: (Carrier sig m, Member (Error Doc) sig, Member Naming sig, Member (Reader ModuleName) sig, Member (Reader Span) sig, Member (State Resolution) sig) => Spanned (Decl User Surface.Surface) -> m (Spanned (Decl Qualified (Core Name)))
resolveDecl (decl :~ span) = (:~ span) <$> case decl of
  Declare n ty -> do
    res <- get
    moduleName <- ask
    ty' <- runReader (res :: Resolution) (runReader Decl (resolveTerm (generalize res ty)))
    Declare (moduleName :.: n) ty' <$ modify (insertGlobal n moduleName)
    where generalize res ty = foldr bind ty (fvs ty Set.\\ Map.keysSet (unResolution res))
          bind n = Surface.Pi (Im :< (Just n, Zero, Surface.Type)) -- FIXME: insert metavariables for the type
  Define n tm -> do
    res <- get
    moduleName <- ask
    tm' <- runReader (res :: Resolution) (runReader Defn (resolveTerm tm))
    Define (moduleName :.: n) tm' <$ modify (insertGlobal n moduleName)
  Doc t d -> Doc t <$> resolveDecl d

resolveModule :: (Carrier sig m, Effect sig, Member (Error Doc) sig, Member Naming sig, Member (Reader Span) sig, Member (State Resolution) sig) => Module User Surface.Surface -> m (Module Qualified (Core Name))
resolveModule m = do
  res <- get
  (res, decls) <- runState (filterResolution amongImports res) (runReader (moduleName m) (traverse resolveDecl (moduleDecls m)))
  modify (<> res)
  pure (m { moduleDecls = decls })
  where amongImports q = any (flip inModule q . importModuleName . unSpanned) (moduleImports m)
        unSpanned (a :~ _) = a

newtype Resolution = Resolution { unResolution :: Map.Map User (NonEmpty Name) }
  deriving (Eq, Ord, Show)

instance Semigroup Resolution where
  Resolution m1 <> Resolution m2 = Resolution (Map.unionWith (fmap nub . (<>)) m1 m2)

insertLocal :: Maybe User -> Gensym -> Resolution -> Resolution
insertLocal (Just n) n' = Resolution . Map.insert n (Local n':|[]) . unResolution
insertLocal Nothing  _  = id

insertGlobal :: User -> ModuleName -> Resolution -> Resolution
insertGlobal n m = Resolution . Map.insertWith (fmap nub . (<>)) n (Global (m:.:n):|[]) . unResolution

lookupName :: User -> Resolution -> Maybe (NonEmpty Name)
lookupName n = Map.lookup n . unResolution

resolveName :: (Carrier sig m, Member (Error Doc) sig, Member Naming sig, Member (Reader Mode) sig, Member (Reader Resolution) sig, Member (Reader Span) sig) => User -> m Name
resolveName v = do
  res <- asks (lookupName v)
  mode <- ask
  res <- case mode of
    Decl -> maybe ((:| []) . Local <$> gensym "") pure res
    Defn -> maybe (freeVariable v)                pure res
  unambiguous v res

filterResolution :: (Name -> Bool) -> Resolution -> Resolution
filterResolution f = Resolution . Map.mapMaybe matches . unResolution
  where matches = nonEmpty . NonEmpty.filter f

unambiguous :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig) => User -> NonEmpty Name -> m Name
unambiguous _ (q:|[]) = pure q
unambiguous v (q:|qs) = ambiguousName v (q :| qs)
