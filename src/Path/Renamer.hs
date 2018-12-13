{-# LANGUAGE FlexibleContexts #-}
module Path.Renamer where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Path.Core
import Path.Elab
import Path.Name
import Path.Surface
import Path.Term
import Text.Trifecta.Rendering (Span)

resolve :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader (Map.Map Name QName)) sig, Member (Reader ModuleName) sig, Member (Reader Resolution) sig, Monad m)
        => Term (Surface Name) Span
        -> m (Term (Surface QName) Span)
resolve (In syn ann) = case syn of
  Core core -> case core of
    Var v -> in' . Core . Var <$> resolveName v ann
    Lam (Just v) b -> do
      moduleName <- ask
      local (Map.insert v (moduleName :.: v)) (in' . Core . Lam (Just (moduleName :.: v)) <$> resolve b)
    Lam Nothing  b -> in' . Core . Lam Nothing <$> resolve b
    f :@ a -> in' . Core <$> ((:@) <$> resolve f <*> resolve a)
    Type -> pure (in' (Core Type))
    Pi (Just v) pi t b -> do
      moduleName <- ask
      in' . Core <$> (Pi (Just (moduleName :.: v)) pi <$> resolve t <*> local (Map.insert v (moduleName :.: v)) (resolve b))
    Pi Nothing pi t b  -> in' . Core <$> (Pi Nothing pi <$> resolve t <*> resolve b)
  a ::: t -> in' <$> ((:::) <$> resolve a <*> resolve t)
  where in' = flip In ann

newtype Resolution = Resolution { unResolution :: Map.Map Name (Set.Set ModuleName) }
  deriving (Eq, Ord, Show)

resolveName :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader (Map.Map Name QName)) sig, Member (Reader Resolution) sig, Monad m) => Name -> Span -> m QName
resolveName v s = asks (Map.lookup v) >>= maybe (asks (Map.lookup v . unResolution) >>= unambiguous v s . maybe [] Set.toList) pure

unambiguous :: (Applicative m, Carrier sig m, Member (Error ElabError) sig) => Name -> Span -> [ModuleName] -> m QName
unambiguous v s []     = throwError (FreeVariable v s)
unambiguous v _ [m]    = pure (m :.: v)
unambiguous v s (m:ms) = throwError (AmbiguousName v s (m :.: v :| map (:.: v) ms))
