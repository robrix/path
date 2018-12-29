{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, StandaloneDeriving, TypeOperators, UndecidableInstances #-}
module Path.Elab where

import Control.Effect hiding ((:+:))
import Control.Effect.Error
import Control.Effect.Reader hiding (Reader(Local))
import Control.Effect.State
import Control.Monad ((<=<), unless, when)
import Data.Foldable (for_)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (catMaybes)
import Data.Traversable (for)
import Path.Back
import Path.Context as Context
import Path.Core as Core
import Path.Env as Env
import Path.Error
import Path.Eval
import Path.Module
import Path.Name
import Path.Plicity
import Path.Resources as Resources
import Path.Semiring
import Path.Synth
import Path.Term
import Path.Usage
import Path.Value as Value
import Text.Trifecta.Rendering (Span)

data Elaborated = Elaborated
  { elaboratedTerm      :: Term (Core Name QName) ()
  , elaboratedResources :: Resources Usage
  , elaboratedType      :: Type QName
  }
  deriving (Eq, Ord, Show)

infer :: ( Carrier sig m
         , Effect sig
         , Member (Error ElabError) sig
         , Member Fresh sig
         , Member (Reader Context) sig
         , Member (Reader Env) sig
         , Member (Reader Usage) sig
         , Monad m
         )
      => Term (Implicit QName :+: Core Name QName) Span
      -> m (Term (Core Name QName) (), Resources Usage, Type QName)
infer (In out span) = case out of
  R Core.Type -> pure (In Core.Type (), mempty, Value.Type)
  R (Core.Pi n i e t b) -> do
    (t', _, _) <- check Value.Type t
    t'' <- eval t'
    (b', _, _) <- n ::: t'' |- check Value.Type b
    pure (In (Core.Pi n i e t' b') (), mempty, Value.Type)
  R (Core.Var n) -> do
    res <- asks (Context.lookup n)
    sigma <- ask
    case res of
      Just t -> pure (In (Core.Var n) (), Resources.singleton n sigma, t)
      _      -> throwError (FreeVariable n span)
  R (f :$ a) -> do
    (f', g1, ft) <- infer f
    case ft of
      Value.Pi _ _ pi t _ -> do
        (a', g2, _) <- check t a
        a'' <- eval a'
        pure (In (f' Core.:$ a') (), g1 <> pi ><< g2, ft `vapp` a'')
      _ -> throwError (IllegalApplication ft (ann f))
  _ -> ask >>= \ ctx -> throwError (NoRuleToInfer (Context.filter (isLocal . getTerm) ctx) span)

check :: ( Carrier sig m
         , Effect sig
         , Member (Error ElabError) sig
         , Member Fresh sig
         , Member (Reader Context) sig
         , Member (Reader Env) sig
         , Member (Reader Usage) sig
         , Monad m
         )
      => Type QName
      -> Term (Implicit QName :+: Core Name QName) Span
      -> m (Term (Core Name QName) (), Resources Usage, Type QName)
check ty (In tm span) = vforce ty >>= \ ty -> case (tm, ty) of
  (L Core.Implicit, ty) -> do
    synthesized <- synth ty
    ctx <- ask
    maybe (throwError (NoRuleToInfer (Context.filter (isLocal . getTerm) ctx) span)) pure synthesized
  (_, Value.Pi tn Im pi t t') -> do
    (b, br, bt) <- tn ::: t |- check t' (In tm span)
    pure (In (Core.Lam tn b) (), br, bt)
  (R (Core.Lam n e), Value.Pi _ _ pi t _) -> do
    (e', res, _) <- n ::: t |- check (ty `vapp` vfree (Local n)) e
    let used = Resources.lookup (Local n) res
    sigma <- ask
    unless (sigma >< pi == More) . when (pi /= used) $
      throwError (ResourceMismatch n pi used span (uses n e))
    pure (In (Core.Lam n e') (), Resources.delete (Local n) res, ty)
  (L (Core.Hole n), ty) -> do
    ctx <- ask
    throwError (TypedHole n ty (Context.filter (isLocal . getTerm) ctx) span)
  (tm, ty) -> do
    v@(_, _, actual) <- infer (In tm span)
    actual' <- vforce actual
    unless (actual' `aeq` ty) (throwError (TypeMismatch ty actual span))
    pure v

(|-) :: (Carrier sig m, Member (Reader Context) sig) => Typed Name -> m a -> m a
n ::: t |- m = local (Context.insert (Local n ::: t)) m

infix 5 |-


type ModuleTable = Map.Map ModuleName (Context, Env)

elabModule :: ( Carrier sig m
              , Effect sig
              , Member (Error ModuleError) sig
              , Member Fresh sig
              , Member (Reader ModuleTable) sig
              , Member (State Context) sig
              , Member (State Env) sig
              , Member (State (Back ElabError)) sig
              , Monad m
              )
           => Module QName (Term (Implicit QName :+: Core Name QName) Span)
           -> m (Module QName (Term (Core Name QName) (), Resources Usage, Type QName))
elabModule m = do
  for_ (moduleImports m) $ \ i -> do
    (ctx, env) <- importModule i
    modify (Context.union ctx)
    modify (Env.union env)

  decls <- for (moduleDecls m) (either ((Nothing <$) . logError) (pure . Just) <=< runError . elabDecl)
  pure m { moduleDecls = catMaybes decls }

logError :: (Carrier sig m, Member (State (Back ElabError)) sig, Monad m) => ElabError -> m ()
logError = modify . flip (:>)

importModule :: ( Carrier sig m
                , Member (Error ModuleError) sig
                , Member (Reader ModuleTable) sig
                , Monad m
                )
             => Import
             -> m (Context, Env)
importModule n = do
  (ctx, env) <- asks (Map.lookup (importModuleName n)) >>= maybe (throwError (UnknownModule n)) pure
  pure (Context.filter (p . getTerm) ctx, Env.filter (const . p) env)
  where p = inModule (importModuleName n)


elabDecl :: ( Carrier sig m
            , Effect sig
            , Member (Error ElabError) sig
            , Member Fresh sig
            , Member (State Context) sig
            , Member (State Env) sig
            , Monad m
            )
         => Decl QName (Term (Implicit QName :+: Core Name QName) Span)
         -> m (Decl QName (Term (Core Name QName) (), Resources Usage, Type QName))
elabDecl = \case
  Declare name ty -> Declare name <$> elabDeclare name ty
  Define  name tm -> Define  name <$> elabDefine  name tm
  Doc docs     d  -> Doc docs <$> elabDecl d

elabDeclare :: ( Carrier sig m
               , Effect sig
               , Member (Error ElabError) sig
               , Member Fresh sig
               , Member (State Context) sig
               , Member (State Env) sig
               , Monad m
               )
            => QName
            -> Term (Implicit QName :+: Core Name QName) Span
            -> m (Term (Core Name QName) (), Resources Usage, Type QName)
elabDeclare name ty = do
  res@(ty', _, _) <- runReader Zero (runContext (runEnv (generalize ty >>= check Value.Type)))
  ty'' <- runEnv (eval ty')
  res <$ modify (Context.insert (name ::: ty''))
  where generalize ty = do
          ctx <- ask
          pure (foldr bind ty (foldMap (\case { Local v -> Set.singleton v ; _ -> mempty }) (fvs ty Set.\\ Context.boundVars ctx)))
        bind n b = In (R (Core.Pi n Im Zero (In (R Core.Type) (ann ty)) b)) (ann ty)

elabDefine :: ( Carrier sig m
              , Effect sig
              , Member (Error ElabError) sig
              , Member Fresh sig
              , Member (State Context) sig
              , Member (State Env) sig
              , Monad m
              )
           => QName
           -> Term (Implicit QName :+: Core Name QName) Span
           -> m (Term (Core Name QName) (), Resources Usage, Type QName)
elabDefine name tm = do
  ty <- gets (Context.lookup name)
  res@(tm', _, ty') <- runReader One (runContext (runEnv (maybe infer check ty tm)))
  tm'' <- runEnv (eval tm')
  modify (Env.insert name tm'')
  res <$ maybe (modify (Context.insert (name ::: ty'))) (const (pure ())) ty

runContext :: (Carrier sig m, Member (State Context) sig, Monad m) => Eff (ReaderC Context m) a -> m a
runContext m = get >>= flip runReader m

runEnv :: (Carrier sig m, Member (State Env) sig, Monad m) => Eff (ReaderC Env m) a -> m a
runEnv m = get >>= flip runReader m
