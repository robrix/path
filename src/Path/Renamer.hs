{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, LambdaCase, TupleSections, TypeOperators #-}
module Path.Renamer where

import Control.Effect
import Control.Effect.Reader hiding (Local)
import Control.Effect.State
import Data.List.NonEmpty as NonEmpty (NonEmpty(..), filter, nonEmpty, nub)
import qualified Data.Map as Map
-- import qualified Data.Set as Set
import GHC.Generics ((:.:) (..))
import Path.Core as Core
import Path.Error
import Path.Module
import Path.Name
import Path.Pretty
import qualified Path.Surface as Surface
import Prelude hiding (pi)
import Text.Trifecta.Rendering (Span, Spanned(..))

type Signature = Map.Map String Gensym

resolveTerm :: ( Carrier sig m
               , Member (Error Doc) sig
               , Member Naming sig
               , Member (Reader Mode) sig
               , Member (Reader Resolution) sig
               , Member (Reader Span) sig
               , Member (State Signature) sig
               )
            => Spanned (Surface.Surface Var)
            -> m (Core (Name Meta))
resolveTerm (term :~ span) = unComp1 (Surface.eiter id (Comp1 . alg) pure pure term) >>= traverse go . Core . Ann span
  where alg (Surface.Lam v (Scope b :~ s)) = unComp1 b >>= fmap (Core . Lam v . Scope . Core . Ann s) . traverse (traverse unComp1)
        alg (f Surface.:$ a) = Core <$> ((:$) <$> ann f <*> traverse ann a)
        alg Surface.Type = pure (Core Type)
        alg (Surface.Pi t (Scope b :~ s)) = fmap Core . Pi <$> traverse (traverse (traverse ann)) t <*> (unComp1 b >>= fmap (Scope . Core . Ann s) . traverse (traverse unComp1))

        ann (b :~ s) = Core . Ann s <$> unComp1 b

        go (M m) = Local . Meta <$> resolveMeta m
        go (U u) = resolveName u


data Mode = Declare | Define
  deriving (Eq, Ord, Show)

resolveDecl :: ( Carrier sig m
               , Effect sig
               , Member (Error Doc) sig
               , Member Naming sig
               , Member (Reader ModuleName) sig
               , Member (State Resolution) sig
               )
            => Spanned (Decl User (Spanned (Surface.Surface Var) ::: Spanned (Surface.Surface Var)))
            -> m (Spanned (Decl Qualified (Core (Name Meta) ::: Core (Name Meta))))
resolveDecl (Decl d n (tm ::: ty) :~ span) = fmap (:~ span) . runReader span $ do
  moduleName <- ask
  -- let vs = fvs ty Set.\\ Map.keysSet (unResolution res)
  --     generalize ty = foldr bind ty vs
  --     bind n ty = do
  --       n' <- gensym (showUser n)
  --       local (insertLocal (Just n) n') $
  --         Pi (Im :< (Just n, Zero, Type)) . Core.bind (Local n') <$> ty -- FIXME: insert metavariables for the type
  res <- evalState (mempty :: Signature) $
    flip (:::) <$> runResolution (runReader Declare (resolveTerm ty))
               <*  modify (insertGlobal n moduleName)
               <*> runResolution (runReader Define  (resolveTerm tm))
  pure (Decl d (moduleName :.: n) res)

runResolution :: (Carrier sig m, Member (State Resolution) sig) => ReaderC Resolution m a -> m a
runResolution m = get >>= \ res -> runReader res m

resolveModule :: ( Carrier sig m
                 , Effect sig
                 , Member (Error Doc) sig
                 , Member Naming sig
                 , Member (State Resolution) sig
                 )
              => Module User (Spanned (Surface.Surface Var) ::: Spanned (Surface.Surface Var))
              -> m (Module Qualified (Core (Name Meta) ::: Core (Name Meta)))
resolveModule m = do
  res <- get
  (res, decls) <- runState (filterResolution amongImports res) (runReader (moduleName m) (traverse resolveDecl (moduleDecls m)))
  modify (<> res)
  pure m { moduleDecls = decls }
  where amongImports q = any (flip inModule q . importModuleName . unSpanned) (moduleImports m)
        unSpanned (a :~ _) = a

newtype Resolution = Resolution { unResolution :: Map.Map User (NonEmpty (Name Meta)) }
  deriving (Eq, Monoid, Ord, Show)

instance Semigroup Resolution where
  Resolution m1 <> Resolution m2 = Resolution (Map.unionWith (fmap nub . (<>)) m1 m2)

insertGlobal :: User -> ModuleName -> Resolution -> Resolution
insertGlobal n m = Resolution . Map.insertWith (fmap nub . (<>)) n (Global (m:.:n):|[]) . unResolution

lookupName :: User -> Resolution -> Maybe (NonEmpty (Name Meta))
lookupName n = Map.lookup n . unResolution

resolveName :: ( Carrier sig m
               , Member (Error Doc) sig
               , Member Naming sig
               , Member (Reader Mode) sig
               , Member (Reader Resolution) sig
               , Member (Reader Span) sig
               )
            => User
            -> m (Name Meta)
resolveName v = do
  res <- asks (lookupName v)
  mode <- ask
  res <- case mode of
    Declare -> maybe ((:| []) . Local . Name <$> gensym "") pure res
    Define  -> maybe (freeVariable v)                       pure res
  unambiguous v res

resolveMeta :: ( Carrier sig m
               , Member Naming sig
               , Member (State Signature) sig
               )
            => String
            -> m Gensym
resolveMeta m = do
  found <- gets (Map.lookup m)
  case found of
    Just meta -> pure meta
    Nothing   -> do
      n <- gensym m
      n <$ modify (Map.insert m n)

filterResolution :: (Name Meta -> Bool) -> Resolution -> Resolution
filterResolution f = Resolution . Map.mapMaybe matches . unResolution
  where matches = nonEmpty . NonEmpty.filter f

unambiguous :: ( Carrier sig m
               , Member (Error Doc) sig
               , Member (Reader Span) sig
               )
            => User
            -> NonEmpty (Name Meta)
            -> m (Name Meta)
unambiguous _ (q:|[]) = pure q
unambiguous v (q:|qs) = ambiguousName v (q :| qs)
