{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, TypeOperators #-}
module Path.Renamer where

import Control.Effect
import Control.Effect.Reader hiding (Local)
import Control.Effect.State
import Data.List.NonEmpty as NonEmpty (NonEmpty(..), filter, nonEmpty, nub)
import qualified Data.Map as Map
import Path.Error
import Path.Module
import Path.Name
import Path.Pretty
import Path.Span
import Path.Surface as Surface
import Prelude hiding (pi)

resolveDecl :: ( Carrier sig m
               , Member (Error Doc) sig
               , Member (Reader ModuleName) sig
               , Member (State Resolution) sig
               , Traversable t
               )
            => Decl (t User)
            -> m (Decl (t Qualified))
-- FIXME: do something with the term/type spans
resolveDecl (Decl n d tm ty) =  do
  moduleName <- ask
  tm' ::: ty' <- flip (:::)
    <$> runSpanned (runResolution . traverse resolveName) ty
    <*  modify (insertGlobal n moduleName)
    <*> runSpanned (runResolution . traverse resolveName) tm
  pure (Decl n d tm' ty')

runResolution :: (Carrier sig m, Member (State Resolution) sig) => ReaderC Resolution m a -> m a
runResolution m = get >>= \ res -> runReader res m

resolveModule :: ( Carrier sig m
                 , Effect sig
                 , Member (Error Doc) sig
                 , Member (State Resolution) sig
                 )
              => Module Surface User
              -> m (Module Surface Qualified)
resolveModule m = do
  res <- get
  (res, decls) <- runState (filterResolution amongImports res) (runReader (moduleName m) (traverse resolveDecl (moduleDecls m)))
  modify (<> res)
  pure m { moduleDecls = decls }
  where amongImports (mn :.: _) = maybe False (const True) (Import mn `Map.lookup` moduleImports m)

newtype Resolution = Resolution { unResolution :: Map.Map User (NonEmpty Qualified) }
  deriving (Eq, Monoid, Ord, Show)

instance Semigroup Resolution where
  Resolution m1 <> Resolution m2 = Resolution (Map.unionWith (fmap nub . (<>)) m1 m2)

insertGlobal :: User -> ModuleName -> Resolution -> Resolution
insertGlobal n m = Resolution . Map.insertWith (fmap nub . (<>)) n ((m:.:n):|[]) . unResolution

lookupName :: User -> Resolution -> Maybe (NonEmpty Qualified)
lookupName n = Map.lookup n . unResolution

resolveName :: ( Carrier sig m
               , Member (Error Doc) sig
               , Member (Reader Resolution) sig
               , Member (Reader Span) sig
               )
            => User
            -> m Qualified
resolveName v = asks (lookupName v) >>= maybe (freeVariable v) (unambiguous v)

filterResolution :: (Qualified -> Bool) -> Resolution -> Resolution
filterResolution f = Resolution . Map.mapMaybe matches . unResolution
  where matches = nonEmpty . NonEmpty.filter f

unambiguous :: ( Carrier sig m
               , Member (Error Doc) sig
               , Member (Reader Span) sig
               )
            => User
            -> NonEmpty Qualified
            -> m Qualified
unambiguous _ (q:|[]) = pure q
unambiguous v (q:|qs) = ambiguousName v (q :| qs)
