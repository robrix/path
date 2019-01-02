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
import Data.Foldable (foldl', for_)
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
import Path.Scope as Scope
import Path.Semiring
import Path.Term
import Path.Usage
import Path.Value as Value
import Text.Trifecta.Rendering (Span)

data Elab m k
  = Infer      (Term (Implicit QName :+: Core Name QName) Span) ((Term (Core Name QName) Type, Resources Usage) -> k)
  | Check Type (Term (Implicit QName :+: Core Name QName) Span) ((Term (Core Name QName) Type, Resources Usage) -> k)
  | forall a . Unify Equation (Type -> m a) (a    -> k)
  | Exists Type                             (Name -> k)

deriving instance Functor (Elab m)

instance HFunctor Elab where
  hmap _ (Infer     tm   k) = Infer     tm         k
  hmap _ (Check  ty tm   k) = Check  ty tm         k
  hmap f (Unify  eq    h k) = Unify  eq    (f . h) k
  hmap _ (Exists ty      k) = Exists ty            k

instance Effect Elab where
  handle state handler (Infer     tm   k) = Infer     tm                            (handler . (<$ state) . k)
  handle state handler (Check  ty tm   k) = Check  ty tm                            (handler . (<$ state) . k)
  handle state handler (Unify  eq    h k) = Unify  eq    (handler . (<$ state) . h) (handler . fmap k)
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
           , Member (Reader [Equation]) sig
           , Member (Reader Context) sig
           , Member (Reader Env) sig
           , Member (Reader Scope) sig
           , Member (Reader Span) sig
           , Member (Reader Usage) sig
           , Monad m
           )
        => Eff (ElabC m) (Term (Core Name QName) Type, Resources Usage)
        -> m (Term (Core Name QName) Type, Resources Usage)
runElab = fmap (\ (sols, (tm, res)) -> (apply sols tm, res)) . runState Nil . evalState mempty . runElabC . interpret
  where apply sols tm = foldl' compose id sols <$> tm
        compose f (m := v ::: _) = f . Value.subst (Local (Meta m)) v

newtype ElabC m a = ElabC { runElabC :: Eff (StateC [Typed Meta] (Eff (StateC (Back Solution) m))) a }
  deriving (Applicative, Functor, Monad)

instance ( Carrier sig m
         , Effect sig
         , Member (Error ElabError) sig
         , Member Fresh sig
         , Member (Reader [Equation]) sig
         , Member (Reader Context) sig
         , Member (Reader Env) sig
         , Member (Reader Scope) sig
         , Member (Reader Span) sig
         , Member (Reader Usage) sig
         , Monad m
         )
      => Carrier (Elab Effect.:+: sig) (ElabC m) where
  ret = ElabC . ret
  eff = handleSum (ElabC . eff . Effect.R . Effect.R . handleCoercible) (\case
    Infer tm k -> withSpan (ann tm) $ case out tm of
      R Core.Type -> k (In Core.Type Value.Type, mempty)
      R (Core.Pi n i e t b) -> do
        (t', _) <- check Value.Type t
        t'' <- eval t'
        (b', _) <- n ::: t'' |- check Value.Type b
        k (In (Core.Pi n i e t' b') Value.Type, mempty)
      R (Core.Var n) -> do
        t <- lookupVar n >>= whnf
        sigma <- ask
        elabImplicits (In (Core.Var n) t) (Resources.singleton n One) (k . fmap (sigma ><<))
        where elabImplicits tm res k
                | Value.Pi Im _ t b <- ann tm = do
                  n <- exists t
                  elabImplicits (In (tm Core.:$ In (Core.Var (Local n)) t) (b (vfree (Local n)))) (Resources.singleton (Local n) One <> res) k
                | otherwise = k (tm, res)
      R (f :$ a) -> do
        (f', g1) <- infer f
        f'' <- whnf (ann f')
        case f'' of
          Value.Pi _ pi t b -> do
            (a', g2) <- check t a
            a'' <- eval a'
            k (In (f' Core.:$ a') (b a''), g1 <> pi ><< g2)
          _ -> throwError (IllegalApplication f'' (ann f))
      _ -> NoRuleToInfer <$> ask <*> ask >>= throwError

    Check ty tm k -> withSpan (ann tm) $ case (out tm, ty) of
      (_, Value.Pi Im pi t t') -> do
        tn <- freshName "_implicit_"
        (b, br) <- tn ::: t |- check (t' (vfree (Local tn))) tm
        verifyResources tn pi br
        k (In (Core.Lam tn b) ty, br)
      (R (Core.Lam n e), Value.Pi Ex pi t b) -> do
        (e', res) <- n ::: t |- check (b (vfree (Local n))) e
        verifyResources n pi res
        k (In (Core.Lam n e') ty, Resources.delete (Local n) res)
      (L (Core.Hole n), ty) -> TypedHole n ty <$> ask <*> ask >>= throwError
      (_, _ :& (_ :.: _)) -> do
        ty' <- whnf ty
        check ty' tm >>= k
      (_, ty) -> do
        (tm', res) <- infer tm
        unify (ty ::: Value.Type :===: ann tm' ::: Value.Type) $ \ unified -> k (tm' { ann = unified }, res)
      where verifyResources n pi br = do
              let used = Resources.lookup (Local n) br
              sigma <- ask
              unless (sigma >< pi == More) . when (pi /= used) $
                ResourceMismatch n pi used <$> ask <*> pure (uses n tm) >>= throwError

    Unify (Value.Type ::: Value.Type :===: Value.Type ::: Value.Type) h k -> h Value.Type >>= k
    Unify q@(Value.Pi p1 u1 t1 b1 ::: Value.Type :===: Value.Pi p2 u2 t2 b2 ::: Value.Type) h k
      | p1 == p2, u1 == u2 -> local (q:) $ do
        n <- freshName "_unify_"
        let vn = vfree (Local n)
        -- FIXME: unification of the body shouldn’t be blocked on unification of the types; that will require split contexts
        unify (t1 ::: Value.Type :===: t2 ::: Value.Type) (\ t ->
          n ::: t |- unify (b1 vn ::: Value.Type :===: b2 vn ::: Value.Type) (\ b -> h (Value.Pi p1 u1 t (flip (Value.subst (Local n)) b)) >>= k))
    Unify q@(f1 ::: Value.Pi p1 u1 t1 b1 :===: f2 ::: Value.Pi p2 u2 t2 b2) h k
      | p1 == p2, u1 == u2 -> local (q:) $ do
        n <- freshName "_unify_"
        let vn = vfree (Local n)
        -- FIXME: unification of the body shouldn’t be blocked on unification of the types; that will require split contexts
        unify (t1 ::: Value.Type :===: t2 ::: Value.Type) (\ t ->
          n ::: t |- unify (f1 $$ vn ::: b1 vn :===: f2 $$ vn ::: b2 vn) (k <=< h))
    Unify q@(Nil :& Local (Meta m1) ::: _ :===: t2 ::: ty2) h k -> local (q:) $ do
      found <- ElabC (lookupMeta m1)
      case found of
        Left (v ::: t) -> unify (v ::: t :===: t2 ::: ty2) h >>= k
        Right t
          -- FIXME: this should only throw for strong rigid occurrences
          | Local (Meta m1) `Set.member` fvs t2 -> ask >>= throwError . InfiniteType (Local (Meta m1)) t2
          | otherwise -> do
            ElabC (modify (List.delete (m1 ::: t)))
            ElabC (modify (:> (m1 := t2 ::: t)))
            h t2 >>= k
    Unify q@(t1 :===: t2@(Nil :& Local (Meta _) ::: _)) h k -> local (q:) $ unify (t2 :===: t1) (k <=< h)
    Unify q@(sp1 :& v1 ::: ty1 :===: sp2 :& v2 ::: ty2) h k
      -- FIXME: Allow twin variables in these positions.
      | v1 == v2, length sp1 == length sp2 -> local (q:) $ do
        ty1 <- lookupVar v1
        ty2 <- lookupVar v2
        unify (ty1 ::: Value.Type :===: ty2 ::: Value.Type) (\ ty ->
          unifySpines ty sp1 sp2 (\ sp -> h (sp :& v1) >>= k))
          where unifySpines _                  Nil         Nil         h = h Nil
                unifySpines (Value.Pi _ _ t b) (as1 :> a1) (as2 :> a2) h = unify (a1 ::: t :===: a2 ::: t) (\ a -> unifySpines (b a) as1 as2 (\ as -> h (as :> a)))
                unifySpines _                  _           _           _ = TypeMismatch (sp1 :& v1 ::: ty1 :===: sp2 :& v2 ::: ty2) <$> ask <*> ask <*> ask >>= throwError
    Unify q@(t1@(_ :& (_ :.: _)) ::: ty1 :===: t2 ::: ty2) h k -> local (q:) $ do
      t1' <- whnf t1
      unify (t1' ::: ty1 :===: t2 ::: ty2) (k <=< h)
    Unify q@(t1 ::: ty1 :===: t2@(_ :& (_ :.: _)) ::: ty2) h k -> local (q:) $ do
      t2' <- whnf t2
      unify (t1 ::: ty1 :===: t2' ::: ty2) (k <=< h)
    Unify q@(t1 ::: ty1 :===: t2 ::: ty2) h k -> local (q:) $ do
      unless (ty1 == ty2) $
        TypeMismatch (ty1 ::: Value.Type :===: ty2 ::: Value.Type) <$> ask <*> ask <*> ask >>= throwError
      unless (t1 == t2) $
        TypeMismatch (t1  ::: ty1        :===: t2  ::: ty2)        <$> ask <*> ask <*> ask >>= throwError
      h t1 >>= k

    Exists ty k -> do
      i <- fresh
      let m = M i
      ElabC (modify ((m ::: ty) :))
      k (Meta m))

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
      => Equation
      -> (Type -> m a)
      -> m a
unify eq m = send (Unify eq m ret)

exists :: (Carrier sig m, Member Elab sig)
       => Type
       -> m Name
exists ty = send (Exists ty ret)


(|-) :: (Carrier sig m, Member (Reader Context) sig) => Typed Name -> m a -> m a
n ::: t |- m = local (Context.insert (n ::: t)) m

infix 5 |-

lookupMeta :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader Span) sig, Member (State [Typed Meta]) sig, Member (State (Back Solution)) sig, Monad m) => Meta -> m (Either (Typed Value) Type)
lookupMeta m =
  foldr (\ m rest -> m >>= maybe rest pure)
        (FreeVariable (Local (Meta m)) <$> ask >>= throwError)
        [ gets (fmap (Left  . solDefn)   . Back.find     ((== m) . solMeta))
        , gets (fmap (Right . typedType) . List.find @[] ((== m) . typedTerm))
        ]

lookupVar :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader Context) sig, Member (Reader Scope) sig, Member (Reader Span) sig, Monad m) => QName -> m Type
lookupVar (m :.: n) = asks (Scope.lookup (m :.: n)) >>= maybe (FreeVariable (m :.: n) <$> ask >>= throwError) (pure . entryType)
lookupVar (Local n) = asks (Context.lookup n) >>= maybe (FreeVariable (Local n) <$> ask >>= throwError) pure

freshName :: (Carrier sig m, Functor m, Member Fresh sig) => String -> m Name
freshName s = Gensym s <$> fresh


withSpan :: (Carrier sig m, Member (Reader Span) sig) => Span -> m a -> m a
withSpan = local . const

runSpan :: (Carrier sig m, Monad m) => (Term f Span -> Eff (ReaderC Span m) a) -> Term f Span -> m a
runSpan f = runReader . ann <*> f

inferRoot :: ( Carrier sig m
             , Effect sig
             , Member (Error ElabError) sig
             , Member Fresh sig
             , Member (Reader Usage) sig
             , Member (State Scope) sig
             , Monad m
             )
          => Term (Implicit QName :+: Core Name QName) Span
          -> m (Term (Core Name QName) Type, Resources Usage)
inferRoot = runScope . runContext . runEnv . runReader ([] :: [Equation]) . runSpan (runElab . infer)

checkRoot :: ( Carrier sig m
             , Effect sig
             , Member (Error ElabError) sig
             , Member Fresh sig
             , Member (Reader Usage) sig
             , Member (State Scope) sig
             , Monad m
             )
          => Type
          -> Term (Implicit QName :+: Core Name QName) Span
          -> m (Term (Core Name QName) Type, Resources Usage)
checkRoot ty = runScope . runContext . runEnv . runReader ([] :: [Equation]) . runSpan (runElab . check ty)


type ModuleTable = Map.Map ModuleName Scope

elabModule :: ( Carrier sig m
              , Effect sig
              , Member (Error ModuleError) sig
              , Member Fresh sig
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
importModule n = asks (Map.lookup (importModuleName n)) >>= maybe (throwError (UnknownModule n)) (pure . Scope.filter (const . inModule (importModuleName n)))


elabDecl :: ( Carrier sig m
            , Effect sig
            , Member (Error ElabError) sig
            , Member Fresh sig
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
               , Member Fresh sig
               , Member (State Scope) sig
               , Monad m
               )
            => QName
            -> Term (Implicit QName :+: Core Name QName) Span
            -> m (Term (Core Name QName) Type, Resources Usage)
elabDeclare name ty = do
  elab <- runReader Zero (checkRoot Value.Type (generalize ty))
  ty' <- runEnv (eval (fst elab))
  elab <$ modify (Scope.insert name (Decl ty'))

generalize :: Term (Implicit QName :+: Core Name QName) Span
           -> Term (Implicit QName :+: Core Name QName) Span
generalize ty = foldr bind ty (localNames (fvs ty))
  where bind n b = In (R (Core.Pi n Im Zero (In (R Core.Type) (ann ty)) b)) (ann ty)

generalizeType :: Type -> Type
generalizeType ty = foldr bind ty (localNames (fvs ty))
  where bind n b = Value.Pi Im Zero Value.Type (flip (Value.subst (Local n)) b)

generalizeValue :: Type -> Value -> Value
generalizeValue = go 0
  where go i (Value.Pi Im _ _ b) v = Value.Lam (const (go (succ i) (b (vfree (Local (Gensym "" i)))) v))
        go _ _                   v = v

elabDefine :: ( Carrier sig m
              , Effect sig
              , Member (Error ElabError) sig
              , Member Fresh sig
              , Member (State Scope) sig
              , Monad m
              )
           => QName
           -> Term (Implicit QName :+: Core Name QName) Span
           -> m (Term (Core Name QName) Type, Resources Usage)
elabDefine name tm = do
  ty <- gets (fmap entryType . Scope.lookup name)
  elab <- runReader One (maybe inferRoot checkRoot ty tm)
  tm' <- runEnv (eval (fst elab))
  elab <$ modify (Scope.insert name (Defn (tm' ::: ann (fst elab))))

runContext :: (Carrier sig m, Monad m) => Eff (ReaderC Context m) a -> m a
runContext = runReader mempty

runEnv :: (Carrier sig m, Monad m) => Eff (ReaderC Env m) a -> m a
runEnv = runReader mempty

runScope :: (Carrier sig m, Member (State Scope) sig, Monad m) => Eff (ReaderC Scope m) a -> m a
runScope m = get >>= flip runReader m
