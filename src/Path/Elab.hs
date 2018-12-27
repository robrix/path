{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, StandaloneDeriving, TypeOperators, UndecidableInstances #-}
module Path.Elab where

import Control.Effect hiding ((:+:))
import Control.Effect.Error
import Control.Effect.Reader hiding (Reader(Local))
import Control.Effect.State
import Control.Monad ((<=<), unless, when)
import Data.Foldable (for_)
import qualified Data.Map as Map
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
import Path.Resources as Resources
import Path.Semiring
import Path.Synth
import Path.Term
import Path.Usage
import Path.Value as Value
import Text.Trifecta.Rendering (Span)

inferEq :: ( Carrier sig m
           , Effect sig
           , Member (Error ElabError) sig
           , Member Fresh sig
           , Member (Reader Context) sig
           , Member (Reader Env) sig
           , Member (Reader Usage) sig
           , Monad m
           )
        => Term (Implicit QName :+: Core Name QName) Span
        -> Term (Implicit QName :+: Core Name QName) Span
        -> m (Term (Core Name QName) (Resources QName Usage, Type QName))
inferEq (In out1 span1) (In out2 _) = case (out1, out2) of
  (R Core.Type, R Core.Type) -> pure (In Core.Type (mempty, Value.Type))
  (R (Core.Pi n1 e1 t1 b1), R (Core.Pi n2 e2 t2 b2)) | n1 == n2 -> do
    t' <- checkEq t1 t2 Value.Type
    t'' <- eval t'
    b' <- local (Context.insert (Local n1) t'') (checkEq b1 b2 Value.Type)
    pure (In (Core.Pi n1 (e1 `max` e2) t' b') (mempty, Value.Type))
  (R (Core.Var n1), R (Core.Var n2)) | n1 == n2 -> do
    res <- asks (Context.lookup n1)
    sigma <- ask
    case res of
      Just t -> pure (In (Core.Var n1) (Resources.singleton n1 sigma, t))
      _      -> throwError (FreeVariable n1 span1)
  (R (f1 :@ a1), R (f2 :@ a2)) -> do
    f' <- inferEq f1 f2
    case ann f' of
      (g1, Value.Pi n pi t t') -> do
        a' <- checkEq a1 a2 t
        let (g2, _) = ann a'
        a'' <- eval a'
        pure (In (f' Core.:@ a') (g1 <> pi ><< g2, subst (Local n) a'' t'))
      _ -> throwError (IllegalApplication (snd (ann f')) (ann f1))
  _ -> ask >>= \ ctx -> throwError (NoRuleToInfer (Context.filter (const . isLocal) ctx) span1)

checkEq :: ( Carrier sig m
           , Effect sig
           , Member (Error ElabError) sig
           , Member Fresh sig
           , Member (Reader Context) sig
           , Member (Reader Env) sig
           , Member (Reader Usage) sig
           , Monad m
           )
        => Term (Implicit QName :+: Core Name QName) Span
        -> Term (Implicit QName :+: Core Name QName) Span
        -> Type QName
        -> m (Term (Core Name QName) (Resources QName Usage, Type QName))
checkEq (In tm1 span1) (In tm2 span2) ty = vforce ty >>= \ ty -> case (tm1, tm2, ty) of
  (L Core.Implicit, L Core.Implicit, ty) -> do
    synthesized <- synth ty
    ctx <- ask
    maybe (throwError (NoRuleToInfer (Context.filter (const . isLocal) ctx) span1)) pure synthesized
  (R (Core.Lam n1 e1), R (Core.Lam n2 e2), Value.Pi tn pi t t') | n1 == n2 -> do
    e' <- local (Context.insert (Local n1) t) (checkEq e1 e2 (subst (Local tn) (vfree (Local n1)) t'))
    let res = fst (ann e')
        used = Resources.lookup (Local n1) res
    sigma <- ask
    unless (sigma >< pi == More) . when (pi /= used) $
      throwError (ResourceMismatch n1 pi used span1 (uses n1 e1))
    pure (In (Core.Lam n1 e') (Resources.delete (Local n1) res, ty))
  (L (Core.Hole n1), L (Core.Hole n2), ty) | n1 == n2 -> do
    ctx <- ask
    throwError (TypedHole n1 ty (Context.filter (const . isLocal) ctx) span1)
  (tm1, tm2, ty) -> do
    v <- inferEq (In tm1 span1) (In tm2 span2)
    actual <- vforce (snd (ann v))
    unless (actual `aeq` ty) (throwError (TypeMismatch ty (snd (ann v)) span1))
    pure v


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
      -> m (Term (Core Name QName) (Resources QName Usage, Type QName))
infer tm = inferEq tm tm

check :: ( Carrier sig m
         , Effect sig
         , Member (Error ElabError) sig
         , Member Fresh sig
         , Member (Reader Context) sig
         , Member (Reader Env) sig
         , Member (Reader Usage) sig
         , Monad m
         )
      => Term (Implicit QName :+: Core Name QName) Span
      -> Type QName
      -> m (Term (Core Name QName) (Resources QName Usage, Type QName))
check tm = checkEq tm tm


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
           -> m (Module QName (Term (Core Name QName) (Resources QName Usage, Type QName)))
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
         => Decl QName (Term (Implicit QName :+: Core Name QName) Span)
         -> m (Decl QName (Term (Core Name QName) (Resources QName Usage, Type QName)))
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
            -> m (Term (Core Name QName) (Resources QName Usage, Type QName))
elabDeclare name ty = do
  ty' <- runReader Zero (runContext (runEnv (check ty Value.Type)))
  ty'' <- runEnv (eval ty')
  ty' <$ modify (Context.insert name ty'')

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
           -> m (Term (Core Name QName) (Resources QName Usage, Type QName))
elabDefine name tm = do
  ty <- gets (Context.lookup name)
  tm' <- runReader One (runContext (runEnv (maybe infer (flip check) ty tm)))
  tm'' <- runEnv (eval tm')
  modify (Env.insert name tm'')
  tm' <$ maybe (modify (Context.insert name (snd (ann tm')))) (const (pure ())) ty

runContext :: (Carrier sig m, Member (State Context) sig, Monad m) => Eff (ReaderC Context m) a -> m a
runContext m = get >>= flip runReader m

runEnv :: (Carrier sig m, Member (State Env) sig, Monad m) => Eff (ReaderC Env m) a -> m a
runEnv m = get >>= flip runReader m
