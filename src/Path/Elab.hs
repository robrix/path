{-# LANGUAGE DeriveFunctor, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, KindSignatures, MultiParamTypeClasses, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.Elab where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.Reader hiding (Reader(Local))
import Control.Effect.State
import Control.Effect.Writer
import Control.Monad ((<=<), unless, when)
import Data.Foldable (for_, toList)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (catMaybes)
import Data.Traversable (for)
import Path.Stack as Stack
import Path.Constraint
import Path.Context as Context
import qualified Path.Core as Core
import Path.Error
import Path.Eval as Eval
import Path.Module
import Path.Name
import Path.Plicity
import Path.Resources as Resources
import Path.Scope as Scope
import Path.Semiring
import Path.Solver
import Path.Usage
import Path.Value as Value hiding (Scope(..))
import Text.Trifecta.Rendering (Span(..))

freshName :: (Carrier sig m, Member Fresh sig, Member (Reader Gensym) sig) => String -> m Qual
freshName s = Local <$> gensym s

context :: (Carrier sig m, Member (Reader Context) sig) => m Context
context = ask

exists' :: (Carrier sig m, Member Fresh sig, Member (Reader Context) sig, Member (Reader Gensym) sig) => Type Meta -> m (Value Meta ::: Type Meta)
exists' ty = do
  ctx <- context
  n <- Meta <$> gensym "meta"
  pure (pure n Value.$$* map (pure . qlocal) (toList (Context.vars ctx)) ::: ty)

goal :: (Carrier sig m, Member (Reader (Type Meta)) sig) => m (Type Meta)
goal = ask

goalIs :: (Carrier sig m, Member (Reader (Type Meta)) sig) => Type Meta -> m a -> m a
goalIs ty = local (const ty)


runElab :: ( Carrier sig m
           , Effect sig
           , Member (Error ElabError) sig
           , Member (Reader Gensym) sig
           , Member (Reader Scope) sig
           )
        => Usage
        -> ReaderC Span (ReaderC Usage (ReaderC Context (WriterC Resources (WriterC (Set.Set (Caused (Equation (Value Meta) ::: Type Meta))) (FreshC m))))) (Value Meta ::: Type Meta)
        -> m (Resources, Value Meta ::: Type Meta)
runElab sigma = local (// "elab") . solveAndApply <=< runFresh . runWriter . runWriter . runReader mempty . runReader sigma . runReader (Span mempty mempty mempty)
  where solveAndApply (eqns, (res, tm ::: ty)) = do
          subst <- solve eqns
          pure (res, apply subst tm ::: apply subst ty)

infer :: (Carrier sig m, Member (Error ElabError) sig, Member Fresh sig, Member (Reader Context) sig, Member (Reader Gensym) sig, Member (Reader Scope) sig, Member (Reader Span) sig, Member (Reader Usage) sig, Member (Writer Resources) sig, Member (Writer (Set.Set (Caused (Equation (Value Meta) ::: Type Meta)))) sig)
      => Core.Core Qual
      -> m (Value Meta ::: Type Meta)
infer = \case
  Core.Type -> pure (Value.Type ::: Value.Type)
  Core.Pi i e t b -> gensym "" >>= \ n -> do
    t' ::: _ <- check (t ::: Value.Type)
    b' ::: _ <- n ::: t' |- check (Core.instantiate (pure (Local n)) b ::: Value.Type)
    pure (Value.pi ((qlocal n, i, e) ::: t') b' ::: Value.Type)
  Core.Var n -> do
    t <- lookupVar n >>= whnf
    sigma <- ask
    tell (Resources.singleton (Qual n) sigma)
    elabImplicits (pure (Qual n) ::: t)
  f Core.:$ a -> do
    f' ::: fTy <- infer f
    (pi, t, b) <- whnf fTy >>= ensurePi
    a' ::: _ <- censor (Resources.mult pi) (check (a ::: t))
    pure (f' $$ a' ::: instantiate a' b)
  Core.Lam b -> gensym "" >>= \ n -> do
    (_, t) <- exists Value.Type
    e' ::: eTy <- n ::: t |- censor (Resources.delete (qlocal n)) (infer (Core.instantiate (pure (Local n)) b))
    pure (Value.lam (qlocal n) e' ::: Value.pi ((qlocal n, Ex, More) ::: t) eTy)
  Core.Hole _ -> do
    (_, ty) <- exists Value.Type
    (_, m) <- exists ty
    pure (m ::: ty)
  Core.Ann ann t -> local (const ann) (infer t)
  where elabImplicits = \case
          tm ::: Value.Pi Im _ t b -> do
            (n, v) <- exists t
            sigma <- ask
            tell (Resources.singleton n sigma)
            elabImplicits (tm $$ v ::: instantiate v b)
          tm -> pure tm

        ensurePi t = case t of
          Value.Pi _ pi t b -> pure (pi, t, b)
          Meta _ Value.:$ _ -> do
            (mA, _A) <- exists Value.Type
            (_, _B) <- exists _A
            let _B' = bind mA _B
            span <- ask
            (More, _A, _B') <$ tell (Set.singleton ((t :===: Value.Pi Ex More _A _B') ::: (Type :: Type Meta) :@ Assert span))
          _ -> throwElabError (IllegalApplication t)

check :: (Carrier sig m, Member (Error ElabError) sig, Member Fresh sig, Member (Reader Context) sig, Member (Reader Gensym) sig, Member (Reader Scope) sig, Member (Reader Span) sig, Member (Reader Usage) sig, Member (Writer Resources) sig, Member (Writer (Set.Set (Caused (Equation (Value Meta) ::: Type Meta)))) sig)
      => Core.Core Qual ::: Type Meta
      -> m (Value Meta ::: Type Meta)
check = \case
  tm ::: ty@(Value.Pi Im pi t b) -> gensym "" >>= \ n -> censor (Resources.delete (qlocal n)) $ do
    (res, e' ::: _) <- n ::: t |- listen (check (tm ::: instantiate (pure (qlocal n)) b))
    verifyResources tm n pi res
    pure (Value.lam (qlocal n) e' ::: ty)
  Core.Lam e ::: ty@(Value.Pi Ex pi t b) -> gensym "" >>= \ n -> censor (Resources.delete (qlocal n)) $ do
    (res, e' ::: _) <- n ::: t |- listen (check (Core.instantiate (pure (Local n)) e ::: instantiate (pure (qlocal n)) b))
    verifyResources (Core.Lam e) n pi res
    pure (Value.lam (qlocal n) e' ::: ty)
  Core.Hole _ ::: ty -> do
    (_, m) <- exists ty
    pure (m ::: ty)
  Core.Ann ann tm ::: ty -> local (const ann) (check (tm ::: ty))
  tm ::: ty@(Qual (_ :.: _) Value.:$ _) -> do
   ty' <- whnf ty
   check (tm ::: ty')
  tm ::: ty -> do
    tm' ::: inferred <- infer tm
    (tm' :::) <$> unify Value.Type (ty :===: inferred)
  where verifyResources tm n pi br = do
          let used = Resources.lookup (qlocal n) br
          sigma <- ask
          unless (sigma >< pi == More) . when (pi /= used) $
            throwElabError (ResourceMismatch n pi used (Core.uses n tm))

        unify ty (tm1 :===: tm2) = if tm1 == tm2 then pure tm1 else do
          (_, v) <- exists ty
          span <- ask
          v <$ tell (Set.fromList [ (v :===: tm1) ::: ty :@ Assert span
                                  , (v :===: tm2) ::: ty :@ Assert span ])

(|-) :: (Carrier sig m, Member (Reader Context) sig) => Gensym ::: Type Meta -> m a -> m a
n ::: t |- m = local (Context.insert (n ::: t)) m

infix 5 |-

throwElabError :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader Context) sig, Member (Reader Span) sig) => ErrorReason -> m a
throwElabError reason = ElabError <$> ask <*> ask <*> pure reason >>= throwError

exists :: (Carrier sig m, Member Fresh sig, Member (Reader Context) sig, Member (Reader Gensym) sig) => Type Meta -> m (Meta, Type Meta)
exists _ = do
  Context c <- ask
  n <- Meta <$> gensym "_meta_"
  pure (n, pure n $$* fmap (pure . qlocal . typedTerm) c)

lookupVar :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader Context) sig, Member (Reader Scope) sig, Member (Reader Span) sig) => Qual -> m (Type Meta)
lookupVar (m :.: n) = asks (Scope.lookup (m :.: n)) >>= maybe (throwElabError (FreeVariable (m :.: n))) (pure . entryType)
lookupVar (Local n) = asks (Context.lookup n)       >>= maybe (throwElabError (FreeVariable (Local n))) pure


type ModuleTable = Map.Map ModuleName Scope

elabModule :: ( Carrier sig m
              , Effect sig
              , Member (Error ModuleError) sig
              , Member (Reader ModuleTable) sig
              , Member (Reader Gensym) sig
              , Member (State (Stack ElabError)) sig
              , Member (State Scope) sig
              )
           => Module Qual (Core.Core Qual)
           -> m (Module Qual (Resources, Value Meta ::: Type Meta))
elabModule m = do
  for_ (moduleImports m) (modify . Scope.union <=< importModule)

  decls <- for (moduleDecls m) (either ((Nothing <$) . logError) (pure . Just) <=< runError . elabDecl)
  pure m { moduleDecls = catMaybes decls }

logError :: (Carrier sig m, Member (State (Stack ElabError)) sig) => ElabError -> m ()
logError = modify . flip (:>)

importModule :: ( Carrier sig m
                , Member (Error ModuleError) sig
                , Member (Reader ModuleTable) sig
                )
             => Import
             -> m Scope
importModule n = asks (Map.lookup (importModuleName n)) >>= maybe (throwError (UnknownModule n)) pure


elabDecl :: ( Carrier sig m
            , Effect sig
            , Member (Error ElabError) sig
            , Member (Reader Gensym) sig
            , Member (State Scope) sig
            )
         => Decl Qual (Core.Core Qual)
         -> m (Decl Qual (Resources, Value Meta ::: Type Meta))
elabDecl = \case
  Declare name ty -> Declare name <$> elabDeclare name ty
  Define  name tm -> Define  name <$> elabDefine  name tm
  Doc docs     d  -> Doc docs <$> elabDecl d

elabDeclare :: ( Carrier sig m
               , Effect sig
               , Member (Error ElabError) sig
               , Member (Reader Gensym) sig
               , Member (State Scope) sig
               )
            => Qual
            -> Core.Core Qual
            -> m (Resources, Value Meta ::: Type Meta)
elabDeclare name ty = do
  elab <- runScope (runElab Zero (check (ty ::: Value.Type)))
  elab <$ modify (Scope.insert name (Decl (typedTerm (snd elab))))

elabDefine :: ( Carrier sig m
              , Effect sig
              , Member (Error ElabError) sig
              , Member (Reader Gensym) sig
              , Member (State Scope) sig
              )
           => Qual
           -> Core.Core Qual
           -> m (Resources, Value Meta ::: Type Meta)
elabDefine name tm = do
  ty <- gets (fmap entryType . Scope.lookup name)
  elab <- runScope (runElab One (maybe (infer tm) (check . (tm :::)) ty))
  elab <$ modify (Scope.insert name (Defn (snd elab)))

runScope :: (Carrier sig m, Member (State Scope) sig) => ReaderC Scope m a -> m a
runScope m = get >>= flip runReader m
