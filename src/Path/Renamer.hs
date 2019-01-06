{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Renamer where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.Reader hiding (Local)
import Control.Effect.State
import Data.Foldable (toList)
import Data.List.NonEmpty as NonEmpty (NonEmpty(..), filter, nonEmpty, nub)
import qualified Data.Map as Map
import Path.Core
import Path.Module
import Path.Name
import Path.Pretty
import Path.Surface
import Path.Term
import Text.Trifecta.Rendering (Span)

resolveTerm :: (Carrier sig m, Member (Error ResolveError) sig, Member Fresh sig, Member (Reader Mode) sig, Member (Reader ModuleName) sig, Member (Reader Resolution) sig, Monad m)
            => Term (Surface (Maybe Name) Name) Span
            -> m (Term (Surface Name QName) Span)
resolveTerm (In syn ann) = case syn of
  R (R (Var v)) -> in' . R . R . Var <$> resolveName v ann
  R (R (Lam v b)) ->
    local (insertLocal v) (in' . R . R <$> (Lam <$> freshen v <*> resolveTerm b))
  R (R (f :$ a)) -> in' . R . R <$> ((:$) <$> resolveTerm f <*> resolveTerm a)
  R (R Type) -> pure (in' (R (R Type)))
  R (R (Pi v ie pi t b)) ->
    in' . R . R <$> (Pi <$> freshen v <*> pure ie <*> pure pi <*> resolveTerm t <*> local (insertLocal v) (resolveTerm b))
  L ((u, a) :-> b) ->
    in' . L <$> ((:->) . (,) u <$> resolveTerm a <*> resolveTerm b)
  R (L (Hole v)) -> in' . R . L . Hole . (:.: v) <$> ask
  where in' = flip In ann

data Mode = Decl | Defn
  deriving (Eq, Ord, Show)

resolveDecl :: (Carrier sig m, Member (Error ResolveError) sig, Member Fresh sig, Member (Reader ModuleName) sig, Member (State Resolution) sig, Monad m) => Decl Name (Term (Surface (Maybe Name) Name) Span) -> m (Decl QName (Term (Surface Name QName) Span))
resolveDecl = \case
  Declare n ty -> do
    res <- get
    moduleName <- ask
    ty' <- runReader (res :: Resolution) (runReader Decl (resolveTerm ty))
    Declare (moduleName :.: n) ty' <$ modify (insertGlobal n moduleName)
  Define n tm -> do
    res <- get
    moduleName <- ask
    tm' <- runReader (res :: Resolution) (runReader Defn (resolveTerm tm))
    Define (moduleName :.: n) tm' <$ modify (insertGlobal n moduleName)
  Doc t d -> Doc t <$> resolveDecl d

resolveModule :: (Carrier sig m, Effect sig, Member (Error ResolveError) sig, Member Fresh sig, Member (State Resolution) sig, Monad m) => Module Name (Term (Surface (Maybe Name) Name) Span) -> m (Module QName (Term (Surface Name QName) Span))
resolveModule m = do
  res <- get
  (res, decls) <- runState (filterResolution amongImports res) (runReader (moduleName m) (traverse resolveDecl (moduleDecls m)))
  modify (<> res)
  pure (m { moduleDecls = decls })
  where amongImports q = any (flip inModule q . importModuleName) (moduleImports m)

newtype Resolution = Resolution { unResolution :: Map.Map Name (NonEmpty QName) }
  deriving (Eq, Ord, Show)

instance Semigroup Resolution where
  Resolution m1 <> Resolution m2 = Resolution (Map.unionWith (fmap nub . (<>)) m1 m2)

insertLocal :: Maybe Name -> Resolution -> Resolution
insertLocal Nothing  = id
insertLocal (Just n) = Resolution . Map.insert n (Local n:|[]) . unResolution

insertGlobal :: Name -> ModuleName -> Resolution -> Resolution
insertGlobal n m = Resolution . Map.insertWith (fmap nub . (<>)) n (m:.:n:|[]) . unResolution

lookupName :: Name -> Resolution -> Maybe (NonEmpty QName)
lookupName n = Map.lookup n . unResolution

resolveName :: (Carrier sig m, Member (Error ResolveError) sig, Member (Reader Mode) sig, Member (Reader Resolution) sig, Monad m) => Name -> Span -> m QName
resolveName v s = do
  res <- asks (lookupName v)
  mode <- ask
  case mode of
    Decl -> maybe (pure (Local v :| [])) pure res >>= unambiguous v s
    Defn -> maybe (throwError (FreeVariable v s)) pure res >>= unambiguous v s

filterResolution :: (QName -> Bool) -> Resolution -> Resolution
filterResolution f = Resolution . Map.mapMaybe matches . unResolution
  where matches = nonEmpty . NonEmpty.filter f

unambiguous :: (Applicative m, Carrier sig m, Member (Error ResolveError) sig) => Name -> Span -> NonEmpty QName -> m QName
unambiguous _ _ (q:|[]) = pure q
unambiguous v s (q:|qs) = throwError (AmbiguousName v s (q :| qs))

freshen :: (Applicative m, Carrier sig m, Member Fresh sig) => Maybe Name -> m Name
freshen Nothing  = Gensym "_" <$> fresh
freshen (Just n) = pure n


data ResolveError
  = FreeVariable Name Span
  | AmbiguousName Name Span (NonEmpty QName)

instance Pretty ResolveError where
  pretty = \case
    FreeVariable name span -> prettyErr (pure span) (pretty "free variable" <+> squotes (pretty name)) []
    AmbiguousName name span sources -> prettyErr (pure span) (pretty "ambiguous name" <+> squotes (pretty name)) [nest 2 (vsep
      ( pretty "it could refer to"
      : map prettyQName (toList sources)))]

instance PrettyPrec ResolveError
