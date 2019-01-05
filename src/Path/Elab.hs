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
import Data.Bifunctor (first)
import Data.Coerce (coerce)
import Data.Foldable (for_)
import qualified Data.Map as Map
import qualified Data.Set as Set
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
  = Infer        (Term (Implicit QName :+: Core Name QName) Span)  ((Resources Usage, Term (Core Name QName) Type) -> k)
  | Check (Typed (Term (Implicit QName :+: Core Name QName) Span)) ((Resources Usage, Term (Core Name QName) Type) -> k)
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
        -> Eff (ElabC m) (Resources Usage, Term (Core Name QName) Type)
        -> m (Set.Set Equation, (Resources Usage, Term (Core Name QName) Type))
runElab sigma = runState mempty . runFresh . runReader mempty . runReader sigma . runElabC . interpret

newtype ElabC m a = ElabC { runElabC :: Eff (ReaderC Usage (Eff (ReaderC Context (Eff (FreshC (Eff (StateC (Set.Set Equation) m))))))) a }
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
    Infer tm k -> case out tm of
      R Core.Type -> k (mempty, In Core.Type Value.Type)
      R (Core.Pi n i e t b) -> do
        (_, t') <- check (t ::: Value.Type)
        (_, b') <- n ::: eval mempty t' |- check (b ::: Value.Type)
        k (mempty, In (Core.Pi n i e t' b') Value.Type)
      R (Core.Var n) -> do
        t <- lookupVar (ann tm) n >>= whnf
        sigma <- askSigma
        elabImplicits (Resources.singleton n One) (In (Core.Var n) t) >>= k . first (sigma ><<)
        where elabImplicits res tm
                | Value.Pi Im _ t b <- ann tm = do
                  n <- exists t
                  elabImplicits (Resources.singleton n One <> res) (In (tm Core.:$ In (Core.Var n) t) (b (vfree n)))
                | otherwise = pure (res, tm)
      R (f Core.:$ a) -> do
        (g1, f') <- infer f
        (pi, t, b) <- whnf (ann f') >>= ensurePi (ann tm)
        (g2, a') <- check (a ::: t)
        k (g1 <> pi ><< g2, In (f' Core.:$ a') (b (eval mempty a')))
      R (Core.Lam n b) -> do
        mt <- exists Value.Type
        let t = vfree mt
        (res, e') <- n ::: t |- infer b
        k (Resources.delete (Local n) res, In (Core.Lam n e') (Value.Pi Ex More t (flip (Value.subst (Local n)) (ann e'))))
      L (Core.Hole _) -> do
        ty <- exists Value.Type
        m <- exists (vfree ty)
        k (mempty, In (Core.Var m) (vfree ty))

    Check (tm ::: ty) k -> case (out tm ::: ty) of
      (_ ::: Value.Pi Im pi t b) -> do
        n <- freshName "_implicit_"
        (res, e') <- n ::: t |- check (tm ::: b (vfree (Local n)))
        verifyResources (ann tm) n pi res
        k (Resources.delete (Local n) res, In (Core.Lam n e') ty)
      (R (Core.Lam n e) ::: Value.Pi Ex pi t b) -> do
        (res, e') <- n ::: t |- check (e ::: b (vfree (Local n)))
        verifyResources (ann tm) n pi res
        k (Resources.delete (Local n) res, In (Core.Lam n e') ty)
      L (Core.Hole _) ::: ty -> do
        m <- exists ty
        k (mempty, In (Core.Var m) ty)
      _ ::: ty -> do
        (res, tm') <- infer tm
        unified <- unify (ty ::: Value.Type :===: ann tm' ::: Value.Type)
        k (res, tm' { ann = unified })
      where verifyResources span n pi br = do
              let used = Resources.lookup (Local n) br
              sigma <- askSigma
              unless (sigma >< pi == More) . when (pi /= used) $
                throwElabError span (ResourceMismatch n pi used (uses n tm)))
    where n ::: t |- ElabC m = ElabC (local (Context.insert (n ::: t)) m)
          infix 5 |-

          ensurePi span t = case t of
            Value.Pi _ pi t b -> pure (pi, t, b)
            Meta _ Value.:$ _ -> do
              mA <- exists Value.Type
              let _A = vfree mA
              mB <- exists _A
              let _B = flip (subst mA) (vfree mB)
              (More, _A, _B) <$ ElabC (modify (Set.insert (t ::: Value.Type :===: Value.Pi Ex More _A _B ::: Value.Type)))
            _ -> throwElabError span (IllegalApplication t)

          unify (tm1 ::: ty1 :===: tm2 ::: ty2) = if tm1 == tm2 then pure tm1 else do
            n <- exists ty1
            let vn = vfree n
            vn <$ ElabC (modify (Set.insert (vn ::: ty1 :===: tm1 ::: ty1) . Set.insert (vn ::: ty1 :===: tm2 ::: ty2)))

          throwElabError span reason = ElabError span <$> askContext <*> pure reason >>= throwError

          askContext = ElabC ask
          askSigma = ElabC ask

          freshName s = Gensym s <$> ElabC fresh
          exists _ = ElabC (Meta . M <$> fresh)

          whnf = ElabC . Eval.whnf

          lookupVar span (m :.: n) = asks (Scope.lookup (m :.: n)) >>= maybe (throwElabError span (FreeVariable (m :.: n))) (pure . entryType)
          lookupVar span (Local n) = ElabC (asks (Context.lookup n)) >>= maybe (throwElabError span (FreeVariable (Local n))) pure
          lookupVar span (Meta n) = throwElabError span (FreeVariable (Meta n))


infer :: (Carrier sig m, Member Elab sig)
      => Term (Implicit QName :+: Core Name QName) Span
      -> m (Resources Usage, Term (Core Name QName) Type)
infer tm = send (Infer tm ret)

check :: (Carrier sig m, Member Elab sig)
      => Typed (Term (Implicit QName :+: Core Name QName) Span)
      -> m (Resources Usage, Term (Core Name QName) Type)
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
           -> m (Module QName (Set.Set Equation, (Resources Usage, Term (Core Name QName) Type)))
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
         -> m (Decl QName (Set.Set Equation, (Resources Usage, Term (Core Name QName) Type)))
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
            -> m (Set.Set Equation, (Resources Usage, Term (Core Name QName) Type))
elabDeclare name ty = do
  elab <- runScope (runElab Zero (check (generalize ty ::: Value.Type)))
  elab <$ modify (Scope.insert name (Decl (eval mempty (snd (snd elab)))))
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
           -> m (Set.Set Equation, (Resources Usage, Term (Core Name QName) Type))
elabDefine name tm = do
  ty <- gets (fmap entryType . Scope.lookup name)
  elab <- runScope (runElab One (maybe (infer tm) (check . (tm :::)) ty))
  elab <$ modify (Scope.insert name (Defn (eval mempty (snd (snd elab)) ::: ann (snd (snd elab)))))

runScope :: (Carrier sig m, Member (State Scope) sig, Monad m) => Eff (ReaderC Scope m) a -> m a
runScope m = get >>= flip runReader m
