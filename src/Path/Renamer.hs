{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, LambdaCase, TupleSections, TypeOperators #-}
module Path.Renamer where

import Control.Effect
import Control.Effect.Reader hiding (Local)
import Control.Effect.State
import Data.List.NonEmpty as NonEmpty (NonEmpty(..), filter, nonEmpty, nub)
import qualified Data.Map as Map
-- import qualified Data.Set as Set
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

type Signature = Map.Map String Gensym

resolveTerm :: ( Carrier sig m
               , Member (Error Doc) sig
               , Member Naming sig
               , Member (Reader Mode) sig
               , Member (Reader ModuleName) sig
               , Member (Reader Resolution) sig
               , Member (Reader Span) sig
               , Member (State Signature) sig
               )
            => Spanned Surface.Surface
            -> m (Core (Name Gensym))
resolveTerm (term :~ span) = local (const span) $ Core . Ann span <$> case term of
  Surface.Var v -> Var <$> resolveName v
  Surface.Lam (p :< v) b -> do
    v' <- gensym (maybe "lam" showUser v)
    local (insertLocal v v') (Core . Lam (p :< v) . bind (Local v') <$> resolveTerm b)
  f Surface.:$ a -> fmap Core . (:$) <$> resolveTerm f <*> traverse resolveTerm a
  Surface.Type -> pure (Core Type)
  Surface.Pi (ie :< v ::: u :@ t) b -> do
    v' <- gensym (maybe "pi" showUser v)
    fmap Core . Pi . (ie :<) . (v :::) . (u :@) <$> resolveTerm t <*> local (insertLocal v v') (bind (Local v') <$> resolveTerm b)
  Surface.Hole v -> Core . Hole <$> resolveMeta v


data Mode = Declare | Define
  deriving (Eq, Ord, Show)

resolveDecl :: ( Carrier sig m
               , Effect sig
               , Member (Error Doc) sig
               , Member Naming sig
               , Member (Reader ModuleName) sig
               , Member (State Resolution) sig
               )
            => Spanned (Decl User (Spanned Surface.Surface ::: Spanned Surface.Surface))
            -> m (Spanned (Decl Qualified (Core (Name Gensym) ::: Core (Name Gensym))))
resolveDecl (Decl d n (tm ::: ty) :~ span) = fmap (:~ span) . runReader span $ do
  moduleName <- ask
  -- let vs = fvs ty Set.\\ Map.keysSet (unResolution res)
  --     generalize ty = foldr bind ty vs
  --     bind n ty = do
  --       n' <- gensym (showUser n)
  --       local (insertLocal (Just n) n') $
  --         Pi (Im :< (Just n, Zero, Type)) . Core.bind (Local n') <$> ty -- FIXME: insert metavariables for the type
  (ty', tm') <- evalState (mempty :: Signature) $
    (,) <$> runResolution (runReader Declare (resolveTerm ty))
        <*  modify (insertGlobal n moduleName)
        <*> runResolution (runReader Define  (resolveTerm tm))
  pure (Decl d (moduleName :.: n) (tm' ::: ty'))

runResolution :: (Carrier sig m, Member (State Resolution) sig) => ReaderC Resolution m a -> m a
runResolution m = get >>= \ res -> runReader res m

resolveModule :: ( Carrier sig m
                 , Effect sig
                 , Member (Error Doc) sig
                 , Member Naming sig
                 , Member (State Resolution) sig
                 )
              => Module User (Spanned Surface.Surface ::: Spanned Surface.Surface)
              -> m (Module Qualified (Core (Name Gensym) ::: Core (Name Gensym)))
resolveModule m = do
  res <- get
  (res, decls) <- runState (filterResolution amongImports res) (runReader (moduleName m) (traverse resolveDecl (moduleDecls m)))
  modify (<> res)
  pure (m { moduleDecls = decls })
  where amongImports q = any (flip inModule q . importModuleName . unSpanned) (moduleImports m)
        unSpanned (a :~ _) = a

newtype Resolution = Resolution { unResolution :: Map.Map User (NonEmpty (Name Gensym)) }
  deriving (Eq, Monoid, Ord, Show)

instance Semigroup Resolution where
  Resolution m1 <> Resolution m2 = Resolution (Map.unionWith (fmap nub . (<>)) m1 m2)

insertLocal :: Maybe User -> Gensym -> Resolution -> Resolution
insertLocal (Just n) n' = Resolution . Map.insert n (Local n':|[]) . unResolution
insertLocal Nothing  _  = id

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

resolveMeta :: ( Carrier sig m
               , Member Naming sig
               , Member (State Signature) sig
               )
            => Maybe String
            -> m Gensym
resolveMeta (Just m) = do
  found <- gets (Map.lookup m)
  case found of
    Just meta -> pure meta
    Nothing   -> do
      n <- gensym m
      n <$ modify (Map.insert m n)
resolveMeta Nothing = gensym "meta"

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
