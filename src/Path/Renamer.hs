{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, TypeOperators #-}
module Path.Renamer where

import Control.Effect
import Control.Effect.Reader hiding (Local)
import Control.Effect.State
import Data.List.NonEmpty as NonEmpty (NonEmpty(..), filter, nonEmpty, nub)
import qualified Data.Map as Map
-- import qualified Data.Set as Set
import Path.Error
import Path.Module
import Path.Name
import Path.Pretty
import Path.Span
import Path.Surface as Surface
import Prelude hiding (pi)

data Mode = Declare | Define
  deriving (Eq, Ord, Show)

resolveDecl :: ( Carrier sig m
               , Member (Error Doc) sig
               , Member Naming sig
               , Member (Reader ModuleName) sig
               , Member (State Resolution) sig
               , Traversable t
               )
            => Decl (t User)
            -> m (Decl (t (Name Gensym)))
-- FIXME: do something with the term/type spans
resolveDecl (Decl n d tm ty) =  do
  moduleName <- ask
  -- let vs = fvs ty Set.\\ Map.keysSet (unResolution res)
  --     generalize ty = foldr bind ty vs
  --     bind n ty = do
  --       n' <- gensym (showUser n)
  --       local (insertLocal (Just n) n') $
  --         Pi (Im :< (Just n, Zero, Type)) . Surface.bind (Local n') <$> ty -- FIXME: insert metavariables for the type
  tm' ::: ty' <- flip (:::)
    <$> runSpanned (run Declare) ty
    <*  modify (insertGlobal n moduleName)
    <*> runSpanned (run Define)  tm
  pure (Decl n d tm' ty')
  where run d = runResolution . runReader d . traverse resolveName

runResolution :: (Carrier sig m, Member (State Resolution) sig) => ReaderC Resolution m a -> m a
runResolution m = get >>= \ res -> runReader res m

resolveModule :: ( Carrier sig m
                 , Effect sig
                 , Member (Error Doc) sig
                 , Member Naming sig
                 , Member (State Resolution) sig
                 )
              => Module Surface User
              -> m (Module Surface (Name Gensym))
resolveModule m = do
  res <- get
  (res, decls) <- runState (filterResolution amongImports res) (runReader (moduleName m) (traverse resolveDecl (moduleDecls m)))
  modify (<> res)
  pure m { moduleDecls = decls }
  where amongImports q = any (flip inModule q . importModuleName . unSpanned) (moduleImports m)
        unSpanned (a :~ _) = a

newtype Resolution = Resolution { unResolution :: Map.Map User (NonEmpty (Name Gensym)) }
  deriving (Eq, Monoid, Ord, Show)

instance Semigroup Resolution where
  Resolution m1 <> Resolution m2 = Resolution (Map.unionWith (fmap nub . (<>)) m1 m2)

insertGlobal :: User -> ModuleName -> Resolution -> Resolution
insertGlobal n m = Resolution . Map.insertWith (fmap nub . (<>)) n (Global (m:.:n):|[]) . unResolution

lookupName :: User -> Resolution -> Maybe (NonEmpty (Name Gensym))
lookupName n = Map.lookup n . unResolution

resolveName :: ( Carrier sig m
               , Member (Error Doc) sig
               , Member Naming sig
               , Member (Reader Mode) sig
               , Member (Reader Resolution) sig
               , Member (Reader Span) sig
               )
            => User
            -> m (Name Gensym)
resolveName v = do
  res <- asks (lookupName v)
  mode <- ask
  res <- case mode of
    Declare -> maybe ((:| []) . Local <$> gensym "") pure res
    Define  -> maybe (freeVariable v)                pure res
  unambiguous v res

filterResolution :: (Name Gensym -> Bool) -> Resolution -> Resolution
filterResolution f = Resolution . Map.mapMaybe matches . unResolution
  where matches = nonEmpty . NonEmpty.filter f

unambiguous :: ( Carrier sig m
               , Member (Error Doc) sig
               , Member (Reader Span) sig
               )
            => User
            -> NonEmpty (Name Gensym)
            -> m (Name Gensym)
unambiguous _ (q:|[]) = pure q
unambiguous v (q:|qs) = ambiguousName v (q :| qs)
