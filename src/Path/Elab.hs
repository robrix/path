{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, StandaloneDeriving, TypeOperators, UndecidableInstances #-}
module Path.Elab where

import Control.Effect hiding ((:+:))
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.Reader hiding (Reader(Local))
import Control.Effect.State
import Control.Monad ((<=<), unless, when)
import Data.Foldable (for_)
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import qualified Data.Set as Set
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
import Path.Subst as Subst
import Path.Term
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
         , Member (State Subst) sig
         , Monad m
         )
      => Term (Implicit QName :+: Core Name QName) Span
      -> m (Term (Core Name QName) (Type QName), Resources Usage)
infer (In out span) = case out of
  R Core.Type -> pure (In Core.Type Value.Type, mempty)
  R (Core.Pi n i e t b) -> do
    (t', _) <- check Value.Type t
    t'' <- eval t'
    (b', _) <- n ::: t'' |- check Value.Type b
    pure (In (Core.Pi n i e t' b') Value.Type, mempty)
  R (Core.Var n) -> do
    res <- asks (Context.lookup n)
    sigma <- ask
    case res of
      Just t -> (,) <$> elabImplicits (In (Core.Var n) t) <*> pure (Resources.singleton n sigma)
      _      -> throwError (FreeVariable n span)
    where elabImplicits tm
            | Value.Pi _ Im _ t _ <- ann tm = do
              n <- Meta . M <$> fresh
              elabImplicits (In (tm Core.:$ In (Core.Var (Local n)) t) (ann tm `vapp` vfree (Local n)))
            | otherwise = pure tm
  R (f :$ a) -> do
    (f', g1) <- infer f
    case ann f' of
      Value.Pi _ _ pi t _ -> do
        (a', g2) <- check t a
        a'' <- eval a'
        pure (In (f' Core.:$ a') (ann f' `vapp` a''), g1 <> pi ><< g2)
      _ -> throwError (IllegalApplication (ann f') (ann f))
  _ -> NoRuleToInfer <$> localVars <*> pure span >>= throwError

check :: ( Carrier sig m
         , Effect sig
         , Member (Error ElabError) sig
         , Member Fresh sig
         , Member (Reader Context) sig
         , Member (Reader Env) sig
         , Member (Reader Usage) sig
         , Member (State Subst) sig
         , Monad m
         )
      => Type QName
      -> Term (Implicit QName :+: Core Name QName) Span
      -> m (Term (Core Name QName) (Type QName), Resources Usage)
check ty (In tm span) = vforce ty >>= \ ty -> case (tm, ty) of
  (_, Value.Pi tn Im pi t t') -> do
    (b, br) <- tn ::: t |- check t' (In tm span)
    let used = Resources.lookup (Local tn) br
    sigma <- ask
    unless (sigma >< pi == More) . when (pi /= used) $
      throwError (ResourceMismatch tn pi used span (uses tn (In tm span)))
    pure (In (Core.Lam tn b) ty, br)
  (R (Core.Lam n e), Value.Pi _ _ pi t _) -> do
    (e', res) <- n ::: t |- check (ty `vapp` vfree (Local n)) e
    let used = Resources.lookup (Local n) res
    sigma <- ask
    unless (sigma >< pi == More) . when (pi /= used) $
      throwError (ResourceMismatch n pi used span (uses n e))
    pure (In (Core.Lam n e') ty, Resources.delete (Local n) res)
  (L (Core.Hole n), ty) -> TypedHole n ty <$> localVars <*> pure span >>= throwError
  (tm, ty) -> do
    v <- infer (In tm span)
    _ <- unify span (ann (fst v)) ty
    pure v

localVars :: (Carrier sig m, Functor m, Member (Reader Context) sig) => m Context
localVars = asks (Context.filter (isLocal . getTerm))

(|-) :: (Carrier sig m, Member (Reader Context) sig) => Typed Name -> m a -> m a
n ::: t |- m = local (Context.insert (Local n ::: t)) m

infix 5 |-


unify :: ( Carrier sig m
         , Member (Error ElabError) sig
         , Member Fresh sig
         , Member (Reader Env) sig
         , Member (State Subst) sig
         , Monad m
         )
      => Span
      -> Type QName
      -> Type QName
      -> m (Type QName)
unify span t1 t2 = go t1 t2
  where unifySpines sp1 sp2 = case (sp1, sp2) of
          (i1 :> l1, i2 :> l2) -> (:>) <$> unifySpines i1 i2 <*> go l1 l2
          (Nil, Nil) -> pure Nil
          _ -> throwError (TypeMismatch t1 t2 span)
        solve m t
          | Local (Meta m) `Set.member` fvs t = throwError (InfiniteType (Local (Meta m)) t span)
          | otherwise                         = do
            extant <- gets (Subst.lookup m)
            case extant of
              Just ty -> go ty t
              Nothing -> t <$ modify (Subst.insert m t)
        go t1 t2 = case (t1, t2) of
          (Value.Type, Value.Type) -> pure Value.Type
          (sp1 Value.:& Local (Meta m1), sp2 Value.:& Local (Meta m2)) -> case compare m1 m2 of
            LT -> solve m2 t1
            EQ -> (:& Local (Meta m1)) <$> unifySpines sp1 sp2
            GT -> solve m1 t2
          (sp1 Value.:& Local (Meta m1), _) -> foldl vapp <$> solve m1 t2 <*> pure sp1
          (_, sp2 Value.:& Local (Meta m2)) -> foldl vapp <$> solve m2 t1 <*> pure sp2
          (Value.Lam _ _, Value.Lam _ _) -> do
            n <- freshName
            Value.Lam n <$> go (t1 `vapp` vfree (Local n)) (t2 `vapp` vfree (Local n))
          (Value.Lam _ _, _) -> do
            n <- freshName
            Value.Lam n <$> go (t1 `vapp` vfree (Local n)) (t2 `vapp` vfree (Local n))
          (_, Value.Lam _ _) -> do
            n <- freshName
            Value.Lam n <$> go (t1 `vapp` vfree (Local n)) (t2 `vapp` vfree (Local n))
          (Value.Pi _ p1 u1 a1 _, Value.Pi _ p2 u2 a2 _) | p1 == p2, u1 == u2 -> do
            n <- freshName
            Value.Pi n p1 u1
              <$> go a1 a2
              <*> go (t1 `vapp` vfree (Local n)) (t2 `vapp` vfree (Local n))
          (sp1 Value.:& h1, sp2 Value.:& h2) | h1 == h2 -> do
            (Value.:& h1) <$> unifySpines sp1 sp2
          (act, exp) -> do
            act' <- vforce act
            unless (exp `aeq` act') (throwError (TypeMismatch exp act span))
            pure act

freshName :: (Carrier sig m, Functor m, Member Fresh sig) => m Name
freshName = Gensym <$> fresh


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
           -> m (Module QName (Term (Core Name QName) (Type QName), Resources Usage))
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
         -> m (Decl QName (Term (Core Name QName) (Type QName), Resources Usage))
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
            -> m (Term (Core Name QName) (Type QName), Resources Usage)
elabDeclare name ty = do
  elab <- runReader Zero (runContext (runEnv (runSubst (generalize ty >>= check Value.Type))))
  ty' <- runEnv (eval (fst elab))
  elab <$ modify (Context.insert (name ::: ty'))
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
           -> m (Term (Core Name QName) (Type QName), Resources Usage)
elabDefine name tm = do
  ty <- gets (Context.lookup name)
  elab <- runReader One (runContext (runEnv (runSubst (maybe infer check ty tm))))
  tm' <- runEnv (eval (fst elab))
  modify (Env.insert name tm')
  elab <$ maybe (modify (Context.insert (name ::: ann (fst elab)))) (const (pure ())) ty

runContext :: (Carrier sig m, Member (State Context) sig, Monad m) => Eff (ReaderC Context m) a -> m a
runContext m = get >>= flip runReader m

runEnv :: (Carrier sig m, Member (State Env) sig, Monad m) => Eff (ReaderC Env m) a -> m a
runEnv m = get >>= flip runReader m
