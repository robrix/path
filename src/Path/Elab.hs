{-# LANGUAGE DeriveFunctor, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, StandaloneDeriving, TypeOperators, UndecidableInstances #-}
module Path.Elab where

import Control.Effect hiding ((:+:))
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.Reader hiding (Reader(Local))
import Control.Effect.State
import Control.Effect.Sum hiding ((:+:)(..))
import qualified Control.Effect.Sum as Effect
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
import Path.Usage
import Path.Value as Value
import Text.Trifecta.Rendering (Span)

data Elab m k
  = Infer      (Term (Implicit QName :+: Core Name QName) Span) ((Term (Core Name QName) Type, Resources Usage) -> k)
  | Check Type (Term (Implicit QName :+: Core Name QName) Span) ((Term (Core Name QName) Type, Resources Usage) -> k)
  | Unify Span Type Type k
  | forall a . Exists Type (Name -> m a) (a -> k)

deriving instance Functor (Elab m)

instance HFunctor Elab where
  hmap _ (Infer      tm k) = Infer      tm      k
  hmap _ (Check   ty tm k) = Check   ty tm      k
  hmap _ (Unify s t1 t2 k) = Unify s t1 t2      k
  hmap f (Exists  ty h  k) = Exists  ty (f . h) k

instance Effect Elab where
  handle state handler (Infer      tm k) = Infer      tm                         (handler . (<$ state) . k)
  handle state handler (Check   ty tm k) = Check   ty tm                         (handler . (<$ state) . k)
  handle state handler (Unify s t1 t2 k) = Unify s t1 t2                         (handler . (<$ state) $ k)
  handle state handler (Exists  ty h  k) = Exists  ty (handler . (<$ state) . h) (handler . fmap k)

runElab :: ( Carrier sig m
           , Effect sig
           , Member (Error ElabError) sig
           , Member Fresh sig
           , Member (Reader Context) sig
           , Member (Reader Env) sig
           , Member (Reader Usage) sig
           , Monad m
           )
        => Eff (ElabC m) a
        -> m a
runElab = evalState mempty . runElabC . interpret

newtype ElabC m a = ElabC { runElabC :: Eff (StateC Context m) a }
  deriving (Applicative, Functor, Monad)

instance ( Carrier sig m
         , Effect sig
         , Member (Error ElabError) sig
         , Member Fresh sig
         , Member (Reader Context) sig
         , Member (Reader Env) sig
         , Member (Reader Usage) sig
         , Monad m
         )
      => Carrier (Elab Effect.:+: sig) (ElabC m) where
  ret = ElabC . ret
  eff = ElabC . handleSum (eff . Effect.R . handleCoercible) (\case
    Infer (In out span) k -> case out of
      R Core.Type -> runElabC (k (In Core.Type Value.type', mempty))
      R (Core.Pi n i e t b) -> do
        (t', _) <- runElabC (check Value.type' t)
        t'' <- eval t'
        (b', _) <- n ::: t'' |- runElabC (check Value.type' b)
        runElabC (k (In (Core.Pi n i e t' b') Value.type', mempty))
      R (Core.Var n) -> runElabC $ do
        res <- asks (Context.lookup n)
        sigma <- ask
        case res of
          Just t -> elabImplicits (In (Core.Var n) t) (Resources.singleton n One) (k . fmap (sigma ><<))
          _      -> throwError (FreeVariable n span)
        where elabImplicits tm res k
                | Value (Value.Pi _ Im _ t _) <- ann tm =
                  exists t $ \ n ->
                    elabImplicits (In (tm Core.:$ In (Core.Var (Local n)) t) (ann tm `vapp` vfree (Local n))) (Resources.singleton (Local n) One <> res) k
                | otherwise = k (tm, res)
      R (f :$ a) -> do
        (f', g1) <- runElabC (infer f)
        case ann f' of
          Value (Value.Pi _ _ pi t _) -> do
            (a', g2) <- runElabC (check t a)
            a'' <- eval a'
            runElabC (k (In (f' Core.:$ a') (ann f' `vapp` a''), g1 <> pi ><< g2))
          _ -> throwError (IllegalApplication (ann f') (ann f))
      _ -> NoRuleToInfer <$> localVars <*> pure span >>= throwError

    Check ty (In tm span) k -> vforce ty >>= \ ty -> case (tm, ty) of
      (_, Value (Value.Pi tn Im pi t t')) -> do
        (b, br) <- tn ::: t |- runElabC (check t' (In tm span))
        let used = Resources.lookup (Local tn) br
        sigma <- ask
        unless (sigma >< pi == More) . when (pi /= used) $
          throwError (ResourceMismatch tn pi used span (uses tn (In tm span)))
        runElabC (k (In (Core.Lam tn b) ty, br))
      (R (Core.Lam n e), Value (Value.Pi _ Ex pi t _)) -> do
        (e', res) <- n ::: t |- runElabC (check (ty `vapp` vfree (Local n)) e)
        let used = Resources.lookup (Local n) res
        sigma <- ask
        unless (sigma >< pi == More) . when (pi /= used) $
          throwError (ResourceMismatch n pi used span (uses n e))
        runElabC (k (In (Core.Lam n e') ty, Resources.delete (Local n) res))
      (L (Core.Hole n), ty) -> TypedHole n ty <$> localVars <*> pure span >>= throwError
      (tm, ty) -> runElabC $ do
        v <- infer (In tm span)
        unify span (ann (fst v)) ty
        k v

    Unify _    (Value Value.Type) (Value Value.Type) k -> runElabC k
    Unify span (Value (Value.Lam n1 b1)) (Value (Value.Lam n2 b2)) k | n1 == n2 -> do
      runElabC (unify span b1 b2 >> k)
    Unify span t1 t2 k -> do
      unless (t1 `aeq` t2) $
        TypeMismatch t1 t2 <$> localVars <*> pure span >>= throwError
      runElabC k

    Exists ty h k -> do
      i <- fresh
      let m = Meta (M i)
      modify (Context.insert (Local m ::: ty))
      runElabC (h m >>= k))

infer :: (Carrier sig m, Member Elab sig)
      => Term (Implicit QName :+: Core Name QName) Span
      -> m (Term (Core Name QName) Type, Resources Usage)
infer tm = send (Infer tm ret)

check :: (Carrier sig m, Member Elab sig)
      => Type
      -> Term (Implicit QName :+: Core Name QName) Span
      -> m (Term (Core Name QName) Type, Resources Usage)
check ty tm = send (Check ty tm ret)


unify :: (Carrier sig m, Member Elab sig)
      => Span
      -> Value
      -> Value
      -> m ()
unify span t1 t2 = send (Unify span t1 t2 (ret ()))

exists :: (Carrier sig m, Member Elab sig)
       => Type
       -> (Name -> m a)
       -> m a
exists ty h = send (Exists ty h ret)


localVars :: (Carrier sig m, Functor m, Member (Reader Context) sig) => m Context
localVars = asks (Context.nub . Context.filter (isLocal . getTerm))

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
  elab <- runReader Zero (runContext (runEnv (runElab (generalize ty >>= check Value.type'))))
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
  elab <- runReader One (runContext (runEnv (runElab (maybe infer check ty tm))))
  tm' <- runEnv (eval (fst elab))
  modify (Env.insert name tm')
  elab <$ maybe (modify (Context.insert (name ::: ann (fst elab)))) (const (pure ())) ty

runContext :: (Carrier sig m, Member (State Context) sig, Monad m) => Eff (ReaderC Context m) a -> m a
runContext m = get >>= flip runReader m

runEnv :: (Carrier sig m, Member (State Env) sig, Monad m) => Eff (ReaderC Env m) a -> m a
runEnv m = get >>= flip runReader m
