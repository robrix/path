{-# LANGUAGE DeriveFunctor, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, KindSignatures, MultiParamTypeClasses, TypeApplications, TypeOperators, UndecidableInstances #-}
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
import Data.Coerce (coerce)
import Data.Foldable (for_)
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import Data.Traversable (for)
import Path.Back as Back
import Path.Context as Context
import Path.Core as Core
import Path.Error
import Path.Eval as Eval
import Path.Module
import Path.Name
import Path.Plicity
import Path.Resources as Resources
import Path.Scope as Scope
import Path.Semiring
import Path.Term
import Path.Type
import Path.Usage
import Path.Value as Value
import Text.Trifecta.Rendering (Span)

data Elab (m :: * -> *) k
  = Infer        (Term (Implicit QName :+: Core Name QName) Span)  ((Term (Core Name QName) Type, Resources Usage) -> k)
  | Check (Typed (Term (Implicit QName :+: Core Name QName) Span)) ((Term (Core Name QName) Type, Resources Usage) -> k)
  deriving (Functor)

instance HFunctor Elab where
  hmap _ = coerce

instance Effect Elab where
  handle state handler = coerce . fmap (handler . (<$ state))


runElab :: ( Carrier sig m
           , Effect sig
           , Member (Error ElabError) sig
           , Member (Reader Scope) sig
           , Monad m
           )
        => Usage
        -> Span
        -> Eff (ElabC m) (Term (Core Name QName) Type, Resources Usage)
        -> m (Term (Core Name QName) Type, Resources Usage)
runElab sigma span = runFresh . runReader mempty . runReader span . runReader sigma . runElabC . interpret

newtype ElabC m a = ElabC { runElabC :: Eff (ReaderC Usage (Eff (ReaderC Span (Eff (ReaderC Context (Eff (FreshC m))))))) a }
  deriving (Applicative, Functor, Monad)

instance ( Carrier sig m
         , Effect sig
         , Member (Error ElabError) sig
         , Member (Reader Scope) sig
         , Monad m
         )
      => Carrier (Elab Effect.:+: sig) (ElabC m) where
  ret = ElabC . ret
  eff = handleSum (ElabC . eff . Effect.R . Effect.R . Effect.R . Effect.R . handleCoercible) (\case
    Infer tm k -> withSpan (ann tm) $ case out tm of
      R Core.Type -> k (In Core.Type Value.Type, mempty)
      R (Core.Pi n i e t b) -> do
        (t', _) <- check (t ::: Value.Type)
        (b', _) <- n ::: eval mempty t' |- check (b ::: Value.Type)
        k (In (Core.Pi n i e t' b') Value.Type, mempty)
      R (Core.Var n) -> do
        t <- lookupVar n >>= whnf
        sigma <- askSigma
        elabImplicits (In (Core.Var n) t) (Resources.singleton n One) >>= k . fmap (sigma ><<)
        where elabImplicits tm res
                | Value.Pi Im _ t b <- ann tm = do
                  n <- exists t
                  elabImplicits (In (tm Core.:$ In (Core.Var (Local n)) t) (b (vfree (Local n)))) (Resources.singleton (Local n) One <> res)
                | otherwise = pure (tm, res)
      R (f Core.:$ a) -> do
        (f', g1) <- infer f
        f'' <- whnf (ann f')
        case f'' of
          Value.Pi _ pi t b -> do
            (a', g2) <- check (a ::: t)
            k (In (f' Core.:$ a') (b (eval mempty a')), g1 <> pi ><< g2)
          _ -> throwElabError (IllegalApplication f'')
      _ -> throwElabError NoRuleToInfer

    Check (tm ::: ty) k -> withSpan (ann tm) $ case (out tm ::: ty) of
      (_ ::: Value.Pi Im pi t b) -> do
        n <- freshName "_implicit_"
        (e', res) <- n ::: t |- check (tm ::: b (vfree (Local n)))
        verifyResources n pi res
        k (In (Core.Lam n e') ty, Resources.delete (Local n) res)
      (R (Core.Lam n e) ::: Value.Pi Ex pi t b) -> do
        (e', res) <- n ::: t |- check (e ::: b (vfree (Local n)))
        verifyResources n pi res
        k (In (Core.Lam n e') ty, Resources.delete (Local n) res)
      L (Core.Hole n) ::: ty -> throwElabError (TypedHole n ty)
      _ ::: ty -> do
        (tm', res) <- infer tm
        unified <- unify (ty ::: Value.Type :===: ann tm' ::: Value.Type)
        k (tm' { ann = unified }, res)
      where verifyResources n pi br = do
              let used = Resources.lookup (Local n) br
              sigma <- askSigma
              unless (sigma >< pi == More) . when (pi /= used) $
                throwElabError (ResourceMismatch n pi used (uses n tm)))
    where n ::: t |- ElabC m = ElabC (local (Context.insert (n ::: t)) m)
          infix 5 |-

          unify q@(t1 ::: _ :===: t2 ::: _) = if t1 == t2 then pure t1 else throwElabError (TypeMismatch q)

          throwElabError reason = ElabError <$> askSpan <*> askContext <*> pure reason >>= throwError

          askContext = ElabC ask
          askSpan = ElabC ask
          askSigma = ElabC ask
          withSpan span (ElabC m) = ElabC (local (const span) m)

          freshName s = Gensym s <$> ElabC fresh
          exists _ = ElabC (Meta . M <$> fresh)

          whnf = ElabC . Eval.whnf

          lookupVar (m :.: n) = asks (Scope.lookup (m :.: n)) >>= maybe (throwElabError (FreeVariable (m :.: n))) (pure . entryType)
          lookupVar (Local n) = ElabC (asks (Context.lookup n)) >>= maybe (throwElabError (FreeVariable (Local n))) pure


infer :: (Carrier sig m, Member Elab sig)
      => Term (Implicit QName :+: Core Name QName) Span
      -> m (Term (Core Name QName) Type, Resources Usage)
infer tm = send (Infer tm ret)

check :: (Carrier sig m, Member Elab sig)
      => Typed (Term (Implicit QName :+: Core Name QName) Span)
      -> m (Term (Core Name QName) Type, Resources Usage)
check tm = send (Check tm ret)


type ModuleTable = Map.Map ModuleName Scope

elabModule :: ( Carrier sig m
              , Effect sig
              , Member (Error ModuleError) sig
              , Member (Reader ModuleTable) sig
              , Member (State (Back ElabError)) sig
              , Member (State Scope) sig
              , Monad m
              )
           => Module QName (Term (Implicit QName :+: Core Name QName) Span)
           -> m (Module QName (Term (Core Name QName) Type, Resources Usage))
elabModule m = do
  for_ (moduleImports m) (modify . Scope.union <=< importModule)

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
             -> m Scope
importModule n = asks (Map.lookup (importModuleName n)) >>= maybe (throwError (UnknownModule n)) pure


elabDecl :: ( Carrier sig m
            , Effect sig
            , Member (Error ElabError) sig
            , Member (State Scope) sig
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
               , Member (State Scope) sig
               , Monad m
               )
            => QName
            -> Term (Implicit QName :+: Core Name QName) Span
            -> m (Term (Core Name QName) Type, Resources Usage)
elabDeclare name ty = do
  elab <- runScope (runElab Zero (ann ty) (check (generalize ty ::: Value.Type)))
  elab <$ modify (Scope.insert name (Decl (eval mempty (fst elab))))
  where generalize ty = foldr bind ty (localNames (fvs ty))
        bind n b = In (R (Core.Pi n Im Zero (In (R Core.Type) (ann ty)) b)) (ann ty)

elabDefine :: ( Carrier sig m
              , Effect sig
              , Member (Error ElabError) sig
              , Member (State Scope) sig
              , Monad m
              )
           => QName
           -> Term (Implicit QName :+: Core Name QName) Span
           -> m (Term (Core Name QName) Type, Resources Usage)
elabDefine name tm = do
  ty <- gets (fmap entryType . Scope.lookup name)
  elab <- runScope (runElab One (ann tm) (maybe (infer tm) (check . (tm :::)) ty))
  elab <$ modify (Scope.insert name (Defn (eval mempty (fst elab) ::: ann (fst elab))))

runScope :: (Carrier sig m, Member (State Scope) sig, Monad m) => Eff (ReaderC Scope m) a -> m a
runScope m = get >>= flip runReader m
