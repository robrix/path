{-# LANGUAGE FlexibleContexts #-}
module Path.Renamer where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as Map
import Path.Core
import Path.Elab
import Path.Name
import Path.Surface
import Path.Term
import Text.Trifecta.Rendering (Span)

resolveTerm :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader ModuleName) sig, Member (Reader Resolution) sig, Monad m)
            => Term (Surface Name) Span
            -> m (Term (Surface QName) Span)
resolveTerm (In syn ann) = case syn of
  Core core -> case core of
    Var v -> in' . Core . Var <$> resolveName v ann
    Lam (Just v) b -> do
      moduleName <- ask
      local (insertLocal v moduleName) (in' . Core . Lam (Just (moduleName :.: v)) <$> resolveTerm b)
    Lam Nothing  b -> in' . Core . Lam Nothing <$> resolveTerm b
    f :@ a -> in' . Core <$> ((:@) <$> resolveTerm f <*> resolveTerm a)
    Type -> pure (in' (Core Type))
    Pi (Just v) pi t b -> do
      moduleName <- ask
      in' . Core <$> (Pi (Just (moduleName :.: v)) pi <$> resolveTerm t <*> local (insertLocal v moduleName) (resolveTerm b))
    Pi Nothing pi t b  -> in' . Core <$> (Pi Nothing pi <$> resolveTerm t <*> resolveTerm b)
  a ::: t -> in' <$> ((:::) <$> resolveTerm a <*> resolveTerm t)
  where in' = flip In ann

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
