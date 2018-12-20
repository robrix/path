{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Renamer where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader hiding (Local)
import Control.Effect.State
import Data.Foldable (toList)
import Data.List.NonEmpty as NonEmpty (NonEmpty(..), filter, nonEmpty, nub)
import qualified Data.Map as Map
import Path.Module
import Path.Name
import Path.Pretty
import Path.Surface
import Path.Term
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import Text.Trifecta.Rendering (Span)

resolveTerm :: (Carrier sig m, Member (Error ResolveError) sig, Member (Reader ModuleName) sig, Member (Reader Resolution) sig, Monad m)
            => Term (Surface Name) Span
            -> m (Term (Surface QName) Span)
resolveTerm (In syn ann) = case syn of
  Var v -> in' . Var <$> resolveName v ann
  Lam v b -> do
    local (insertLocal v) (in' . Lam (Local v) <$> resolveTerm b)
  f :@ a -> in' <$> ((:@) <$> resolveTerm f <*> resolveTerm a)
  Type -> pure (in' Type)
  Pi v pi t b -> do
    in' <$> (Pi (Local v) pi <$> resolveTerm t <*> local (insertLocal v) (resolveTerm b))
  a ::: t -> in' <$> ((:::) <$> resolveTerm a <*> resolveTerm t)
  ForAll v t b -> do
    in' <$> (ForAll (Local v) <$> resolveTerm t <*> local (insertLocal v) (resolveTerm b))
  Hole v -> in' . Hole . (:.: v) <$> ask
  where in' = flip In ann

resolveDecl :: (Carrier sig m, Member (Error ResolveError) sig, Member (Reader ModuleName) sig, Member (State Resolution) sig, Monad m) => Decl Name (Term (Surface Name) Span) -> m (Decl QName (Term (Surface QName) Span))
resolveDecl = \case
  Declare n ty -> do
    res <- get
    moduleName <- ask
    ty' <- runReader (res :: Resolution) (resolveTerm ty)
    Declare (moduleName :.: n) ty' <$ modify (insertGlobal n moduleName)
  Define n tm -> do
    res <- get
    moduleName <- ask
    tm' <- runReader (res :: Resolution) (resolveTerm tm)
    Define (moduleName :.: n) tm' <$ modify (insertGlobal n moduleName)
  Doc t d -> Doc t <$> resolveDecl d

resolveModule :: (Carrier sig m, Effect sig, Member (Error ResolveError) sig, Member (State Resolution) sig, Monad m) => Module Name (Term (Surface Name) Span) Span -> m (Module QName (Term (Surface QName) Span) Span)
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

insertLocal :: Name -> Resolution -> Resolution
insertLocal n = Resolution . Map.insert n (Local n:|[]) . unResolution

insertGlobal :: Name -> ModuleName -> Resolution -> Resolution
insertGlobal n m = Resolution . Map.insertWith (fmap nub . (<>)) n (m:.:n:|[]) . unResolution

lookupName :: Name -> Resolution -> Maybe (NonEmpty QName)
lookupName n = Map.lookup n . unResolution

resolveName :: (Carrier sig m, Member (Error ResolveError) sig, Member (Reader Resolution) sig, Monad m) => Name -> Span -> m QName
resolveName v s = asks (lookupName v) >>= maybe (throwError (FreeVariable v s)) pure >>= unambiguous v s

filterResolution :: (QName -> Bool) -> Resolution -> Resolution
filterResolution f = Resolution . Map.mapMaybe matches . unResolution
  where matches = nonEmpty . NonEmpty.filter f

unambiguous :: (Applicative m, Carrier sig m, Member (Error ResolveError) sig) => Name -> Span -> NonEmpty QName -> m QName
unambiguous _ _ (q:|[]) = pure q
unambiguous v s (q:|qs) = throwError (AmbiguousName v s (q :| qs))


data ResolveError
  = FreeVariable Name Span
  | AmbiguousName Name Span (NonEmpty QName)

instance Pretty ResolveError where
  pretty = \case
    FreeVariable name span -> prettyErr span (pretty "free variable" <+> squotes (pretty name)) Nothing
    AmbiguousName name span sources -> prettyErr span (pretty "ambiguous name" <+> squotes (pretty name)) (Just (nest 2 (vsep
      ( pretty "it could refer to"
      : map prettyQName (toList sources)))))

instance PrettyPrec ResolveError
