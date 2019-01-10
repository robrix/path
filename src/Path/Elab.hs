{-# LANGUAGE DeriveFunctor, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, KindSignatures, MultiParamTypeClasses, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.Elab where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Fresh
import Control.Effect.Reader hiding (Reader(Local))
import Control.Effect.State
import Control.Effect.Sum
import Control.Effect.Writer
import Control.Monad ((<=<), unless, when)
import Data.Coerce (coerce)
import Data.Foldable (for_)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (catMaybes)
import Data.Traversable (for)
import Path.Stack as Stack
import Path.Constraint
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
import Path.Solver
import Path.Term
import Path.Usage
import Path.Value as Value hiding (Scope(..))
import Text.Trifecta.Rendering (Span)

data Elab (m :: * -> *) k
  = Infer        (Term (Core Name QName) Span)  (Typed Value -> k)
  | Check (Typed (Term (Core Name QName) Span)) (Typed Value -> k)
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
        -> Eff (ElabC m) (Typed Value)
        -> m (Resources, Typed Value)
runElab sigma = runFresh . (solveAndApply <=< runWriter . runWriter . runReader mempty . runReader sigma . runElabC . interpret)
  where solveAndApply (eqns, (res, tm ::: ty)) = do
          subst <- solve eqns
          pure (res, apply subst tm ::: apply subst ty)

newtype ElabC m a = ElabC { runElabC :: Eff (ReaderC Usage (Eff (ReaderC Context (Eff (WriterC Resources (Eff (WriterC (Set.Set (Caused (Equation Value))) (Eff (FreshC m))))))))) a }
  deriving (Applicative, Functor, Monad)

instance ( Carrier sig m
         , Effect sig
         , Member (Error ElabError) sig
         , Member (Reader Scope) sig
         , Monad m
         )
      => Carrier (Elab :+: sig) (ElabC m) where
  ret = ElabC . ret
  eff = handleSum (ElabC . eff . R . R . R . R . R . handleCoercible) (\case
    Infer tm k -> k =<< case out tm of
      Core.Type -> pure (Value.Type ::: Value.Type)
      Core.Pi n i e t b -> do
        t' ::: _ <- check (t ::: Value.Type)
        b' ::: _ <- n ::: t' |- check (b ::: Value.Type)
        pure (Value.pi ((n, i, e) ::: t') b' ::: Value.Type)
      Core.Free n -> do
        t <- lookupVar (ann tm) n >>= whnf
        sigma <- askSigma
        ElabC (tell (Resources.singleton n sigma))
        elabImplicits (free (n ::: t) ::: t)
      Core.Bound i | let n = Local (Gensym "" i) -> do
        t <- lookupVar (ann tm) n >>= whnf
        sigma <- askSigma
        ElabC (tell (Resources.singleton n sigma))
        elabImplicits (free (n ::: t) ::: t)
      f Core.:$ a -> do
        f' ::: fTy <- infer f
        (pi, t, b) <- whnf fTy >>= ensurePi (ann tm)
        a' ::: _ <- raise (censor (Resources.mult pi)) (check (a ::: t))
        pure (f' $$ a' ::: instantiate a' b)
      Core.Lam n b -> do
        (_, t) <- exists Value.Type
        e' ::: eTy <- n ::: t |- raise (censor (Resources.delete (Local n))) (infer b)
        pure (Value.lam (n ::: t) e' ::: Value.pi ((n, Ex, More) ::: t) eTy)
      Core.Hole _ -> do
        (_, ty) <- exists Value.Type
        (_, m) <- exists ty
        pure (m ::: ty)

    Check (tm ::: ty) k -> k =<< case (out tm ::: ty) of
      _ ::: Value.Pi Im pi t b -> freshName "_implicit_" >>= \ n -> raise (censor (Resources.delete (Local n))) $ do
        (res, e' ::: _) <- n ::: t |- raise listen (check (tm ::: instantiate (free (Local n ::: t)) b))
        verifyResources (ann tm) n pi res
        pure (Value.lam (n ::: t) e' ::: ty)
      Core.Lam n e ::: Value.Pi Ex pi t b -> raise (censor (Resources.delete (Local n))) $ do
        (res, e' ::: _) <- n ::: t |- raise listen (check (e ::: instantiate (free (Local n ::: t)) b))
        verifyResources (ann tm) n pi res
        pure (Value.lam (n ::: t) e' ::: ty)
      Core.Hole _ ::: ty -> do
        (_, m) <- exists ty
        pure (m ::: ty)
      _ ::: ((Value.Free (_ :.: _) ::: _) Value.:$ _) -> do
       ty' <- whnf ty
       check (tm ::: ty')
      _ ::: ty -> do
        tm' ::: inferred <- infer tm
        unified <- unify (ann tm) Value.Type (ty :===: inferred)
        pure (tm' ::: unified)
      where verifyResources span n pi br = do
              let used = Resources.lookup (Local n) br
              sigma <- askSigma
              unless (sigma >< pi == More) . when (pi /= used) $
                throwElabError span (ResourceMismatch n pi used (uses n tm)))
    where n ::: t |- m = raise (local (Context.insert (n ::: t))) m
          infix 5 |-
          raise f (ElabC m) = ElabC (f m)

          elabImplicits = \case
            tm ::: Value.Pi Im _ t b -> do
              (n, v) <- exists t
              sigma <- askSigma
              ElabC (tell (Resources.singleton n sigma))
              elabImplicits (tm $$ v ::: instantiate v b)
            tm -> pure tm

          ensurePi span t = case t of
            Value.Pi _ pi t b -> pure (pi, t, b)
            (Value.Free (Meta _) ::: _) Value.:$ _ -> do
              (mA, _A) <- exists Value.Type
              (_, _B) <- exists _A
              let _B' = bind mA _B
              (More, _A, _B') <$ ElabC (tell (Set.singleton (t :===: Value.Pi Ex More _A _B' :@ Assert span)))
            _ -> throwElabError span (IllegalApplication t)

          unify span ty (tm1 :===: tm2) = if tm1 == tm2 then pure tm1 else do
            (_, v) <- exists ty
            v <$ ElabC (tell (Set.fromList [ (v :===: tm1 :@ Assert span)
                                           , (v :===: tm2 :@ Assert span) ]))

          throwElabError span reason = ElabError span <$> askContext <*> pure reason >>= throwError

          askContext = ElabC ask
          askSigma = ElabC ask

          freshName s = Gensym s <$> ElabC fresh
          exists t = do
            Context c <- askContext
            n <- Meta . M <$> ElabC fresh
            pure (n, free (n ::: abstractPi (fmap Local <$> c) t) $$* fmap (free . fmap Local) c)

          lookupVar span (m :.: n) = asks (Scope.lookup (m :.: n)) >>= maybe (throwElabError span (FreeVariable (m :.: n))) (pure . entryType)
          lookupVar span (Local n) = ElabC (asks (Context.lookup n)) >>= maybe (throwElabError span (FreeVariable (Local n))) pure
          lookupVar span (Meta n) = throwElabError span (FreeVariable (Meta n))


infer :: (Carrier sig m, Member Elab sig)
      => Term (Core Name QName) Span
      -> m (Typed Value)
infer tm = send (Infer tm ret)

check :: (Carrier sig m, Member Elab sig)
      => Typed (Term (Core Name QName) Span)
      -> m (Typed Value)
check tm = send (Check tm ret)


type ModuleTable = Map.Map ModuleName Scope

elabModule :: ( Carrier sig m
              , Effect sig
              , Member (Error ModuleError) sig
              , Member (Reader ModuleTable) sig
              , Member (State (Stack ElabError)) sig
              , Member (State Scope) sig
              , Monad m
              )
           => Module QName (Term (Core Name QName) Span)
           -> m (Module QName (Resources, Typed Value))
elabModule m = do
  for_ (moduleImports m) (modify . Scope.union <=< importModule)

  decls <- for (moduleDecls m) (either ((Nothing <$) . logError) (pure . Just) <=< runError . elabDecl)
  pure m { moduleDecls = catMaybes decls }

logError :: (Carrier sig m, Member (State (Stack ElabError)) sig, Monad m) => ElabError -> m ()
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
         => Decl QName (Term (Core Name QName) Span)
         -> m (Decl QName (Resources, Typed Value))
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
            -> Term (Core Name QName) Span
            -> m (Resources, Typed Value)
elabDeclare name ty = do
  elab <- runScope (runElab Zero (check (generalize ty ::: Value.Type)))
  elab <$ modify (Scope.insert name (Decl (typedTerm (snd elab))))
  where generalize ty = foldr bind ty (localNames (fvs ty))
        bind n b = In (Core.Pi n Im Zero (In Core.Type (ann ty)) b) (ann ty)

elabDefine :: ( Carrier sig m
              , Effect sig
              , Member (Error ElabError) sig
              , Member (State Scope) sig
              , Monad m
              )
           => QName
           -> Term (Core Name QName) Span
           -> m (Resources, Typed Value)
elabDefine name tm = do
  ty <- gets (fmap entryType . Scope.lookup name)
  elab <- runScope (runElab One (maybe (infer tm) (check . (tm :::)) ty))
  elab <$ modify (Scope.insert name (Defn (snd elab)))

runScope :: (Carrier sig m, Member (State Scope) sig, Monad m) => Eff (ReaderC Scope m) a -> m a
runScope m = get >>= flip runReader m
