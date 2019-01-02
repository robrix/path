{-# LANGUAGE DeriveFunctor, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, StandaloneDeriving, TypeApplications, TypeOperators, UndecidableInstances #-}
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
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import qualified Data.Set as Set
import Data.Traversable (for)
import Path.Back as Back
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
  | forall a . Unify (Typed Value) (Typed Value) (Type -> m a) (a    -> k)
  | Exists Type                                                (Name -> k)

deriving instance Functor (Elab m)

instance HFunctor Elab where
  hmap _ (Infer     tm   k) = Infer     tm         k
  hmap _ (Check  ty tm   k) = Check  ty tm         k
  hmap f (Unify  t1 t2 h k) = Unify  t1 t2 (f . h) k
  hmap _ (Exists ty      k) = Exists ty            k

instance Effect Elab where
  handle state handler (Infer     tm   k) = Infer     tm                            (handler . (<$ state) . k)
  handle state handler (Check  ty tm   k) = Check  ty tm                            (handler . (<$ state) . k)
  handle state handler (Unify  t1 t2 h k) = Unify  t1 t2 (handler . (<$ state) . h) (handler . fmap k)
  handle state handler (Exists ty      k) = Exists ty                               (handler . (<$ state) . k)

data Solution
  = Meta := Typed Value
  deriving (Eq, Ord, Show)

infix 5 :=

solMeta :: Solution -> Meta
solMeta (m := _) = m

solDefn :: Solution -> Typed Value
solDefn (_ := d) = d

solValue :: Solution -> Value
solValue = typedTerm . solDefn

solType :: Solution -> Type
solType = typedType . solDefn


runElab :: ( Carrier sig m
           , Effect sig
           , Member (Error ElabError) sig
           , Member Fresh sig
           , Member (Reader Context) sig
           , Member (Reader Env) sig
           , Member (Reader Span) sig
           , Member (Reader Usage) sig
           , Monad m
           )
        => Eff (ElabC m) a
        -> m a
runElab = evalState Nil . evalState mempty . runElabC . interpret

newtype ElabC m a = ElabC { runElabC :: Eff (StateC [Typed Meta] (Eff (StateC (Back Solution) m))) a }
  deriving (Applicative, Functor, Monad)

instance ( Carrier sig m
         , Effect sig
         , Member (Error ElabError) sig
         , Member Fresh sig
         , Member (Reader Context) sig
         , Member (Reader Env) sig
         , Member (Reader Span) sig
         , Member (Reader Usage) sig
         , Monad m
         )
      => Carrier (Elab Effect.:+: sig) (ElabC m) where
  ret = ElabC . ret
  eff = ElabC . handleSum (eff . Effect.R . Effect.R . handleCoercible) (\case
    Infer tm k -> withSpan (ann tm) $ case out tm of
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
          _      -> FreeVariable n <$> ask >>= throwError
        where elabImplicits tm res k
                | Value (Value.Pi _ Im _ t _) <- ann tm = do
                  n <- exists t
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
      _ -> NoRuleToInfer <$> localVars <*> ask >>= throwError

    Check ty tm k -> withSpan (ann tm) $ vforce ty >>= \ ty -> case (out tm, ty) of
      (_, Value (Value.Pi tn Im pi t t')) -> do
        (b, br) <- tn ::: t |- runElabC (check t' tm)
        let used = Resources.lookup (Local tn) br
        sigma <- ask
        unless (sigma >< pi == More) . when (pi /= used) $
          ResourceMismatch tn pi used <$> ask <*> pure (uses tn tm) >>= throwError
        runElabC (k (In (Core.Lam tn b) ty, br))
      (R (Core.Lam n e), Value (Value.Pi _ Ex pi t _)) -> do
        (e', res) <- n ::: t |- runElabC (check (ty `vapp` vfree (Local n)) e)
        let used = Resources.lookup (Local n) res
        sigma <- ask
        unless (sigma >< pi == More) . when (pi /= used) $
          ResourceMismatch n pi used <$> ask <*> pure (uses n e) >>= throwError
        runElabC (k (In (Core.Lam n e') ty, Resources.delete (Local n) res))
      (L (Core.Hole n), ty) -> TypedHole n ty <$> localVars <*> ask >>= throwError
      (_, ty) -> runElabC $ do
        (tm', res) <- infer tm
        unify (ann tm' ::: type') (ty ::: type') $ \ unified -> k (tm' { ann = unified }, res)

    Unify (Value Value.Type ::: Value Value.Type) (Value Value.Type ::: Value Value.Type) h k -> runElabC (h Value.type' >>= k)
    Unify (Value (Value.Pi n1 p1 u1 t1 b1) ::: Value Value.Type) (Value (Value.Pi n2 p2 u2 t2 b2) ::: Value Value.Type) h k
      | n1 == n2, p1 == p2, u1 == u2 ->
        -- FIXME: unification of the body shouldn’t be blocked on unification of the types; that will require split contexts
        runElabC (unify (t1 ::: type') (t2 ::: type') (\ t ->
          n1 ::: t |- unify (b1 ::: t) (b2 ::: t) (\ b -> h (Value.piType n1 p1 u1 t b) >>= k)))
    Unify (Value (Nil :& Local (Meta m1)) ::: _) (t2 ::: ty2) h k -> do
      found <- lookupMeta m1
      case found of
        Nothing -> FreeVariable (Local (Meta m1)) <$> ask >>= throwError
        Just (Left (v ::: t)) -> runElabC (unify (v ::: t) (t2 ::: ty2) h >>= k)
        Just (Right t) -> do
          modify (List.delete (m1 ::: t))
          modify (:> (m1 := t2 ::: t))
          runElabC (h t2 >>= k)
    Unify (t1 ::: ty1) (t2 ::: ty2) h k -> do
      unless (ty1 `aeq` ty2 && t1 `aeq` t2) $
        TypeMismatch t1 t2 <$> localVars <*> ask >>= throwError
      runElabC (h t1 >>= k)

    Exists ty k -> do
      i <- fresh
      let m = M i
      modify ((m ::: ty) :)
      runElabC (k (Meta m)))

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
      => Typed Value
      -> Typed Value
      -> (Type -> m a)
      -> m a
unify t1 t2 m = send (Unify t1 t2 m ret)

exists :: (Carrier sig m, Member Elab sig)
       => Type
       -> m Name
exists ty = send (Exists ty ret)


localVars :: (Carrier sig m, Functor m, Member (Reader Context) sig) => m Context
localVars = asks (Context.nub . Context.filter (isLocal . typedTerm))

(|-) :: (Carrier sig m, Member (Reader Context) sig) => Typed Name -> m a -> m a
n ::: t |- m = local (Context.insert (Local n ::: t)) m

infix 5 |-

lookupMeta :: (Carrier sig m, Member (State [Typed Meta]) sig, Member (State (Back Solution)) sig, Monad m) => Meta -> m (Maybe (Either (Typed Value) Type))
lookupMeta m = do
  soln <- gets (fmap (Left . solDefn) . Back.find ((== m) . solMeta))
  maybe (gets (fmap (Right . typedType) . List.find @[] ((== m) . typedTerm))) (pure . Just) soln


withSpan :: (Carrier sig m, Member (Reader Span) sig) => Span -> m a -> m a
withSpan = local . const

runSpan :: (Carrier sig m, Monad m) => (Term f Span -> Eff (ReaderC Span m) a) -> Term f Span -> m a
runSpan f = runReader . ann <*> f

inferRoot :: ( Carrier sig m
             , Effect sig
             , Member (Error ElabError) sig
             , Member Fresh sig
             , Member (Reader Usage) sig
             , Member (State Context) sig
             , Member (State Env) sig
             , Monad m
             )
          => Term (Implicit QName :+: Core Name QName) Span
          -> m (Term (Core Name QName) Type, Resources Usage)
inferRoot = runContext . runEnv . runSpan (runElab . infer)

checkRoot :: ( Carrier sig m
             , Effect sig
             , Member (Error ElabError) sig
             , Member Fresh sig
             , Member (Reader Usage) sig
             , Member (State Context) sig
             , Member (State Env) sig
             , Monad m
             )
          => Type
          -> Term (Implicit QName :+: Core Name QName) Span
          -> m (Term (Core Name QName) Type, Resources Usage)
checkRoot ty = runContext . runEnv . runSpan (runElab . check ty)


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
  pure (Context.filter (p . typedTerm) ctx, Env.filter (const . p) env)
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
  elab <- runReader Zero (generalize ty >>= checkRoot Value.type')
  ty' <- runEnv (eval (fst elab))
  elab <$ modify (Context.insert (name ::: ty'))
  where generalize ty = do
          ctx <- get
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
  elab <- runReader One (maybe inferRoot checkRoot ty tm)
  tm' <- runEnv (eval (fst elab))
  modify (Env.insert name tm')
  elab <$ maybe (modify (Context.insert (name ::: ann (fst elab)))) (const (pure ())) ty

runContext :: (Carrier sig m, Member (State Context) sig, Monad m) => Eff (ReaderC Context m) a -> m a
runContext m = get >>= flip runReader m

runEnv :: (Carrier sig m, Member (State Env) sig, Monad m) => Eff (ReaderC Env m) a -> m a
runEnv m = get >>= flip runReader m
