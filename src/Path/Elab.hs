{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, StandaloneDeriving, UndecidableInstances #-}
module Path.Elab where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader hiding (Reader(Local))
import Control.Effect.State
import Control.Monad ((<=<), unless, when)
import Data.Foldable (for_)
import qualified Data.Map as Map
import Path.Context as Context
import Path.Core as Core
import Path.Env as Env
import Path.Error
import Path.Eval
import Path.Module
import Path.Name
import Path.Resources as Resources
import Path.Semiring
import Path.Surface as Surface
import Path.Synth
import Path.Term
import Path.Unify
import Path.Usage
import Path.Value as Value
import Text.Trifecta.Rendering (Span)

infer :: ( Carrier sig m
         , Effect sig
         , Member (Error ElabError) sig
         , Member Fresh sig
         , Member (Reader Context) sig
         , Member (Reader Env) sig
         , Member (Reader Usage) sig
         , Monad m
         )
      => Term (Surface QName) Span
      -> m (Term Core (Resources QName Usage, Type QName))
infer (In out span) = case out of
  ForAll n t b -> do
    t' <- check t Value.Type
    t'' <- eval t'
    b' <- local (Context.insert (Local n) t'') (check b Value.Type)
    pure (In (Core.Pi n Zero t' b') (mempty, Value.Type))
  Surface.Type -> pure (In Core.Type (mempty, Value.Type))
  Surface.Pi n e t b -> do
    t' <- check t Value.Type
    t'' <- eval t'
    b' <- local (Context.insert (Local n) t'') (check b Value.Type)
    pure (In (Core.Pi n e t' b') (mempty, Value.Type))
  Surface.Var n -> do
    res <- asks (Context.lookup n)
    sigma <- ask
    case res of
      Just t -> pure (In (Core.Var n) (Resources.singleton n sigma, t))
      _      -> throwError (FreeVariable n span)
  f Surface.:@ a -> do
    f' <- infer f
    case ann f' of
      (g1, Value.Pi n pi t t') -> do
        a' <- check a t
        let (g2, _) = ann a'
        a'' <- eval a'
        pure (In (f' Core.:@ a') (g1 <> pi ><< g2, subst (Local n) a'' t'))
      _ -> throwError (IllegalApplication (() <$ f') (snd (ann f')) (ann f))
  _ -> ask >>= \ ctx -> throwError (NoRuleToInfer (Context.filter (const . isLocal) ctx) span)

check :: ( Carrier sig m
         , Effect sig
         , Member (Error ElabError) sig
         , Member Fresh sig
         , Member (Reader Context) sig
         , Member (Reader Env) sig
         , Member (Reader Usage) sig
         , Monad m
         )
      => Term (Surface QName) Span
      -> Type QName
      -> m (Term Core (Resources QName Usage, Type QName))
check (In tm span) ty = vforce ty >>= \ ty -> case (tm, ty) of
  (Surface.Implicit, ty) -> do
    synthesized <- synth ty
    ctx <- ask
    maybe (throwError (NoRuleToInfer (Context.filter (const . isLocal) ctx) span)) pure synthesized
  (Surface.Lam n e, Value.Pi tn pi t t') -> do
    e' <- local (Context.insert (Local n) t) (check e (subst (Local tn) (vfree (Local n)) t'))
    let res = fst (ann e')
        used = Resources.lookup (Local n) res
    sigma <- ask
    unless (sigma >< pi == More) . when (pi /= used) $
      throwError (ResourceMismatch n pi used span (uses n e))
    pure (In (Core.Lam n e') (Resources.delete (Local n) res, Value.Pi tn pi t t'))
  (Surface.Hole n, ty) -> do
    ctx <- ask
    throwError (TypedHole n ty (Context.filter (const . isLocal) ctx) span)
  (tm, ty) -> do
    v <- infer (In tm span)
    ty' <- unify span Value.Type (snd (ann v)) ty
    pure (In (out v) (fst (ann v), ty'))


type ModuleTable = Map.Map ModuleName (Context, Env)

elabModule :: ( Carrier sig m
              , Effect sig
              , Member (Error ModuleError) sig
              , Member Fresh sig
              , Member (Reader ModuleTable) sig
              , Member (State [ElabError]) sig
              )
           => Module QName (Term (Surface QName) Span) Span
           -> m (Context, Env)
elabModule m = runState (mempty :: Context) . execState (mempty :: Env) $ do
  for_ (moduleImports m) $ \ i -> do
    (ctx, env) <- importModule i
    modify (Context.union ctx)
    modify (Env.union env)

  for_ (moduleDecls m) (either logError pure <=< runError . elabDecl)

logError :: (Carrier sig m, Member (State [ElabError]) sig, Monad m) => ElabError -> m ()
logError = modify . (:)

importModule :: ( Carrier sig m
                , Member (Error ModuleError) sig
                , Member (Reader ModuleTable) sig
                , Monad m
                )
             => Import Span
             -> m (Context, Env)
importModule n = do
  (ctx, env) <- asks (Map.lookup (importModuleName n)) >>= maybe (throwError (UnknownModule n)) pure
  pure (Context.filter p ctx, Env.filter p env)
  where p = const . inModule (importModuleName n)


elabDecl :: ( Carrier sig m
            , Effect sig
            , Member (Error ElabError) sig
            , Member Fresh sig
            , Member (State Context) sig
            , Member (State Env) sig
            , Monad m
            )
         => Decl QName (Term (Surface QName) Span)
         -> m ()
elabDecl = \case
  Declare name ty -> elabDeclare name ty
  Define  name tm -> elabDefine  name tm
  Doc _        d  -> elabDecl d

elabDeclare :: ( Carrier sig m
               , Effect sig
               , Member (Error ElabError) sig
               , Member Fresh sig
               , Member (State Context) sig
               , Member (State Env) sig
               , Monad m
               )
            => QName
            -> Term (Surface QName) Span
            -> m ()
elabDeclare name ty = do
  ty' <- runReader Zero (runContext (runEnv (check ty Value.Type)))
  ty'' <- runEnv (eval ty')
  modify (Context.insert name ty'')

elabDefine :: ( Carrier sig m
              , Effect sig
              , Member (Error ElabError) sig
              , Member Fresh sig
              , Member (State Context) sig
              , Member (State Env) sig
              , Monad m
              )
           => QName
           -> Term (Surface QName) Span
           -> m ()
elabDefine name tm = do
  ty <- gets (Context.lookup name)
  tm' <- runReader One (runContext (runEnv (maybe infer (flip check) ty tm)))
  tm'' <- runEnv (eval tm')
  modify (Env.insert name tm'')
  maybe (modify (Context.insert name (snd (ann tm')))) (const (pure ())) ty

runContext :: (Carrier sig m, Member (State Context) sig, Monad m) => Eff (ReaderC Context m) a -> m a
runContext m = get >>= flip runReader m

runEnv :: (Carrier sig m, Member (State Env) sig, Monad m) => Eff (ReaderC Env m) a -> m a
runEnv m = get >>= flip runReader m
