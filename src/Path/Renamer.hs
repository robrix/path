{-# LANGUAGE FlexibleContexts #-}
module Path.Renamer where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader hiding (Local)
import Control.Effect.State
import Data.Foldable (toList)
import Data.List.NonEmpty (NonEmpty(..), nub)
import qualified Data.Map as Map
import Path.Decl
import Path.Module
import Path.Name
import Path.Pretty
import Path.Surface
import Path.Term
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import Text.Trifecta.Rendering (Span, render)

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
resolveDecl (Declare n ty) = do
  res <- get
  moduleName <- ask
  ty' <- runReader (res :: Resolution) (resolveTerm ty)
  Declare (moduleName :.: n) ty' <$ modify (insertGlobal n moduleName)
resolveDecl (Define n tm) = do
  res <- get
  moduleName <- ask
  tm' <- runReader (res :: Resolution) (resolveTerm tm)
  Define (moduleName :.: n) tm' <$ modify (insertGlobal n moduleName)

resolveModule :: (Carrier sig m, Member (Error ResolveError) sig, Member (State Resolution) sig, Monad m) => Module Name (Term (Surface Name) Span) -> m (Module QName (Term (Surface QName) Span))
resolveModule m = do
  decls <- runReader (moduleName m) (traverse resolveDecl (moduleDecls m))
  pure (m { moduleDecls = decls })

newtype Resolution = Resolution { unResolution :: Map.Map Name (NonEmpty QName) }
  deriving (Eq, Ord, Show)

insertLocal :: Name -> Resolution -> Resolution
insertLocal n = Resolution . Map.insert n (Local n:|[]) . unResolution

insertGlobal :: Name -> ModuleName -> Resolution -> Resolution
insertGlobal n m = Resolution . Map.insertWith (fmap nub . (<>)) n (m:.:n:|[]) . unResolution

lookupName :: Name -> Resolution -> Maybe (NonEmpty QName)
lookupName n = Map.lookup n . unResolution

resolveName :: (Carrier sig m, Member (Error ResolveError) sig, Member (Reader Resolution) sig, Monad m) => Name -> Span -> m QName
resolveName v s = asks (lookupName v) >>= maybe (throwError (FreeVariable v s)) pure >>= unambiguous v s

unambiguous :: (Applicative m, Carrier sig m, Member (Error ResolveError) sig) => Name -> Span -> NonEmpty QName -> m QName
unambiguous _ _ (q:|[]) = pure q
unambiguous v s (q:|qs) = throwError (AmbiguousName v s (q :| qs))


data ResolveError
  = FreeVariable Name Span
  | AmbiguousName Name Span (NonEmpty QName)

instance Pretty ResolveError where
  pretty (FreeVariable name span) = nest 2 $ pretty "free variable" <+> squotes (pretty name) <$$> pretty (render span)
  pretty (AmbiguousName name span sources) = nest 2 $ vsep
    [ pretty "ambiguous name" <+> squotes (pretty name)
    , nest 2 $ vsep
      ( pretty "it could refer to"
      : map pretty (toList sources))
    , prettys span
    ]

instance PrettyPrec ResolveError
