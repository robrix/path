{-# LANGUAGE FlexibleContexts #-}
module Path.Renamer where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader
import Control.Effect.State
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as Map
import Path.Decl
import Path.Elab
import Path.Module
import Path.Name
import Path.Surface
import Path.Term
import Text.Trifecta.Rendering (Span)

resolveTerm :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader ModuleName) sig, Member (Reader Resolution) sig, Monad m)
            => Term (Surface Name) Span
            -> m (Term (Surface QName) Span)
resolveTerm (In syn ann) = case syn of
  Var v -> in' . Var <$> resolveName v ann
  Lam v b -> do
    moduleName <- ask
    local (insertLocal v moduleName) (in' . Lam (moduleName :.: v) <$> resolveTerm b)
  f :@ a -> in' <$> ((:@) <$> resolveTerm f <*> resolveTerm a)
  Type -> pure (in' Type)
  Pi v pi t b -> do
    moduleName <- ask
    in' <$> (Pi (moduleName :.: v) pi <$> resolveTerm t <*> local (insertLocal v moduleName) (resolveTerm b))
  a ::: t -> in' <$> ((:::) <$> resolveTerm a <*> resolveTerm t)
  ForAll v t b -> do
    moduleName <- ask
    in' <$> (ForAll (moduleName :.: v) <$> resolveTerm t <*> local (insertLocal v moduleName) (resolveTerm b))
  where in' = flip In ann

resolveDecl :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader ModuleName) sig, Member (State Resolution) sig, Monad m) => Decl Name (Term (Surface Name) Span) -> m (Decl QName (Term (Surface QName) Span))
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

resolveModule :: (Carrier sig m, Member (Error ElabError) sig, Member (State Resolution) sig, Monad m) => Module Name (Term (Surface Name) Span) -> m (Module QName (Term (Surface QName) Span))
resolveModule m = do
  decls <- runReader (moduleName m) (traverse resolveDecl (moduleDecls m))
  pure (m { moduleDecls = decls })

newtype Resolution = Resolution { unResolution :: Map.Map Name (NonEmpty ModuleName) }
  deriving (Eq, Ord, Show)

insertLocal :: Name -> ModuleName -> Resolution -> Resolution
insertLocal n m = Resolution . Map.insert n (m:|[]) . unResolution

insertGlobal :: Name -> ModuleName -> Resolution -> Resolution
insertGlobal n m = Resolution . Map.insertWith (<>) n (m:|[]) . unResolution

lookupName :: Name -> Resolution -> Maybe (NonEmpty ModuleName)
lookupName n = Map.lookup n . unResolution

resolveName :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader Resolution) sig, Monad m) => Name -> Span -> m QName
resolveName v s = asks (Map.lookup v . unResolution) >>= maybe (throwError (FreeVariable v s)) pure >>= unambiguous v s

unambiguous :: (Applicative m, Carrier sig m, Member (Error ElabError) sig) => Name -> Span -> NonEmpty ModuleName -> m QName
unambiguous v _ (m:|[]) = pure (m :.: v)
unambiguous v s (m:|ms) = throwError (AmbiguousName v s (m :.: v :| map (:.: v) ms))
