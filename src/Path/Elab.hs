{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, KindSignatures, LambdaCase, MultiParamTypeClasses, StandaloneDeriving, TypeOperators, UndecidableInstances #-}
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
import Path.Term
import Path.Unify
import Path.Usage
import Path.Value as Value
import Text.Trifecta.Rendering (Span)

data Elab (m :: * -> *) k
  = Infer      (Term (Implicit QName :+: Core Name QName) Span) ((Term (Core Name QName) Type, Resources Usage) -> k)
  | Check Type (Term (Implicit QName :+: Core Name QName) Span) ((Term (Core Name QName) Type, Resources Usage) -> k)
  | Assume Type (Meta -> k)
  deriving (Functor)

infer :: ( Carrier sig m
         , Effect sig
         , Member (Error ElabError) sig
         , Member Fresh sig
         , Member (Reader Context) sig
         , Member (Reader Env) sig
         , Member (Reader Usage) sig
         , Member (State Constraint) sig
         , Monad m
         )
      => Term (Implicit QName :+: Core Name QName) Span
      -> m (Term (Core Name QName) Type, Resources Usage)
infer (In out span) = case out of
  R Core.Type -> pure (In Core.Type Value.type', mempty)
  R (Core.Pi n i e t b) -> do
    (t', _) <- check Value.type' t
    t'' <- eval t'
    (b', _) <- n ::: t'' |- check Value.type' b
    pure (In (Core.Pi n i e t' b') Value.type', mempty)
  R (Core.Var n) -> do
    res <- asks (Context.lookup n)
    sigma <- ask
    case res of
      Just t -> (,) <$> elabImplicits (In (Core.Var n) t) <*> pure (Resources.singleton n sigma)
      _      -> throwError (FreeVariable n span)
    where elabImplicits tm
            | Value (Value.Pi _ Im _ t _) <- ann tm = do
              n <- freshMeta
              elabImplicits (In (tm Core.:$ In (Core.Var (Local n)) t) (ann tm `vapp` vfree (Local n)))
            | otherwise = pure tm
  R (f :$ a) -> do
    (f', g1) <- infer f
    case ann f' of
      Value (Value.Pi _ _ pi t _) -> do
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
         , Member (State Constraint) sig
         , Monad m
         )
      => Type
      -> Term (Implicit QName :+: Core Name QName) Span
      -> m (Term (Core Name QName) Type, Resources Usage)
check ty (In tm span) = vforce ty >>= \ ty -> case (tm, ty) of
  (_, Value (Value.Pi tn Im pi t t')) -> do
    (b, br) <- tn ::: t |- check t' (In tm span)
    let used = Resources.lookup (Local tn) br
    sigma <- ask
    unless (sigma >< pi == More) . when (pi /= used) $
      throwError (ResourceMismatch tn pi used span (uses tn (In tm span)))
    pure (In (Core.Lam tn b) ty, br)
  (R (Core.Lam n e), Value (Value.Pi _ _ pi t _)) -> do
    (e', res) <- n ::: t |- check (ty `vapp` vfree (Local n)) e
    let used = Resources.lookup (Local n) res
    sigma <- ask
    unless (sigma >< pi == More) . when (pi /= used) $
      throwError (ResourceMismatch n pi used span (uses n e))
    pure (In (Core.Lam n e') ty, Resources.delete (Local n) res)
  (L (Core.Hole n), ty) -> TypedHole n ty <$> localVars <*> pure span >>= throwError
  (tm, ty) -> do
    v <- infer (In tm span)
    unless (ann (fst v) `aeq` ty) $
      TypeMismatch (ann (fst v)) ty <$> localVars <*> pure span >>= throwError
    pure v

localVars :: (Carrier sig m, Functor m, Member (Reader Context) sig) => m Context
localVars = asks (Context.nub . Context.filter (isLocal . getTerm))

(|-) :: (Carrier sig m, Member (Reader Context) sig) => Typed Name -> m a -> m a
n ::: t |- m = local (Context.insert (Local n ::: t)) m

infix 5 |-


freshName :: (Carrier sig m, Functor m, Member Fresh sig) => m Name
freshName = Gensym <$> fresh

freshMeta :: (Carrier sig m, Functor m, Member Fresh sig) => m Name
freshMeta = Meta . M <$> fresh


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
           -> m (Module QName (Term (Core Name QName) Type, Resources Usage))
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
         -> m (Decl QName (Term (Core Name QName) Type, Resources Usage))
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
            -> m (Term (Core Name QName) Type, Resources Usage)
elabDeclare name ty = do
  elab <- runReader Zero (runContext (runEnv (runConstraints (generalize ty >>= check Value.type'))))
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
           -> m (Term (Core Name QName) Type, Resources Usage)
elabDefine name tm = do
  ty <- gets (Context.lookup name)
  elab <- runReader One (runContext (runEnv (runConstraints (maybe infer check ty tm))))
  tm' <- runEnv (eval (fst elab))
  modify (Env.insert name tm')
  elab <$ maybe (modify (Context.insert (name ::: ann (fst elab)))) (const (pure ())) ty

runContext :: (Carrier sig m, Member (State Context) sig, Monad m) => Eff (ReaderC Context m) a -> m a
runContext m = get >>= flip runReader m

runEnv :: (Carrier sig m, Member (State Env) sig, Monad m) => Eff (ReaderC Env m) a -> m a
runEnv m = get >>= flip runReader m
