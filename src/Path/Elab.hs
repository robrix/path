{-# LANGUAGE DeriveFunctor, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, KindSignatures, MultiParamTypeClasses, StandaloneDeriving, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.Elab where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Reader hiding (Reader(Local))
import Control.Effect.State
import Control.Effect.Sum
import Control.Effect.Writer
import Control.Monad ((<=<))
import Data.Foldable (for_)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (catMaybes)
import Data.Traversable (for)
import Path.Stack as Stack
import Path.Constraint
import Path.Context as Context
import qualified Path.Core as Core
import Path.Error
import Path.Module
import Path.Name
import Path.Plicity
import Path.Pretty
import Path.Scope as Scope
import Path.Semiring
import Path.Solver
import Path.Usage
import Path.Value (Type, Value(..))
import qualified Path.Value as Value
import Prelude hiding (pi)
import Text.Trifecta.Rendering (Span(..), Spanned(..))

assume :: (Carrier sig m, Member Elab sig, Member (Error Doc) sig, Member (Reader Span) sig)
       => Name
       -> m (Value Meta)
assume v = do
  _A <- have v >>= maybe (freeVariable v) pure
  -- FIXME: ???
  pure (pure (Name v))

intro :: (Carrier sig m, Member Elab sig, Member Naming sig)
      => Maybe User
      -> (Name -> m (Value Meta))
      -> m (Value Meta)
intro x body = do
  _A <- exists Type
  x <- gensym (maybe "_" showUser x)
  _B <- x ::: _A |- exists Type
  u <- x ::: _A |- goalIs _B (body (Local x))
  pure (Value.lam (Name (Local x)) u)

pi :: (Carrier sig m, Member Elab sig, Member Naming sig)
   => Maybe User
   -> Plicity
   -> Usage
   -> m (Value Meta)
   -> (Name -> m (Value Meta))
   -> m (Value Meta)
pi x p m t body = do
  t' <- goalIs Type t
  x <- gensym (maybe "_" showUser x)
  b' <- x ::: t' |- goalIs Type (body (Local x))
  pure (Value.pi ((qlocal x, p, m) ::: t') b')

app :: (Carrier sig m, Member Elab sig, Member Naming sig)
    => m (Value Meta)
    -> m (Value Meta)
    -> m (Value Meta)
app f a = do
  _A <- exists Type
  _B <- exists Type
  x <- gensym "app"
  f' <- goalIs (Value.pi ((qlocal x, Ex, zero) ::: _A) _B) f
  a' <- goalIs _A a
  pure (f' Value.$$ a')


exists :: (Carrier sig m, Member Elab sig)
       => Type Meta
       -> m (Value Meta)
exists ty = send (Exists ty pure)

goalIs :: (Carrier sig m, Member Elab sig) => Type Meta -> m a -> m a
goalIs ty m = send (GoalIs ty m pure)

unify :: (Carrier sig m, Member Elab sig)
      => Equation (Value Meta ::: Type Meta)
      -> m ()
unify q = send (Unify q (pure ()))

(|-) :: (Carrier sig m, Member Elab sig) => Gensym ::: Type Meta -> m a -> m a
b |- m = send (Bind b m pure)

infix 5 |-

have :: (Carrier sig m, Member Elab sig) => Name -> m (Maybe (Type Meta))
have n = send (Have n pure)


spanIs :: (Carrier sig m, Member (Reader Span) sig) => Span -> m a -> m a
spanIs span = local (const span)

elab :: (Carrier sig m, Member Elab sig, Member (Error Doc) sig, Member Naming sig, Member (Reader Span) sig)
     => Core.Core Name
     -> m (Value Meta)
elab = \case
  Core.Var n -> assume n
  Core.Lam n b -> intro n (\ n' -> elab (Core.instantiate (pure n') b))
  f Core.:$ a -> app (elab f) (elab a)
  Core.Type -> pure Type
  Core.Pi n p m t b -> pi n p m (elab t) (\ n' -> elab (Core.instantiate (pure n') b))
  Core.Hole _ -> do
    ty <- exists Type
    exists ty
  Core.Ann ann b -> spanIs ann (elab b)


data Elab m k
  = Exists (Type Meta) (Value Meta -> k)
  | forall a . GoalIs (Type Meta) (m a) (a -> k)
  | Have Name (Maybe (Type Meta) -> k)
  | forall a . Bind (Gensym ::: Type Meta) (m a) (a -> k)
  | Unify (Equation (Value Meta ::: Type Meta)) k

deriving instance Functor (Elab m)

instance HFunctor Elab where
  hmap f = \case
    Exists t   k -> Exists t       k
    GoalIs t m k -> GoalIs t (f m) k
    Have   n   k -> Have   n       k
    Bind   b m k -> Bind   b (f m) k
    Unify  q   k -> Unify  q       k

instance Effect Elab where
  handle state handler = \case
    Exists t   k -> Exists t                        (handler . (<$ state) . k)
    GoalIs t m k -> GoalIs t (handler (m <$ state)) (handler . fmap k)
    Have   n   k -> Have   n                        (handler . (<$ state) . k)
    Bind   b m k -> Bind   b (handler (m <$ state)) (handler . fmap k)
    Unify  q   k -> Unify  q                        (handler (k <$ state))


runElab :: Type Meta
        -> ElabC m a
        -> m (Set.Set Constraint, a)
runElab ty = runWriter . runReader mempty . runReader ty . runElabC

newtype ElabC m a = ElabC { runElabC :: ReaderC (Type Meta) (ReaderC (Context (Type Meta)) (WriterC (Set.Set Constraint) m)) a }
  deriving (Applicative, Functor, Monad)

instance (Carrier sig m, Effect sig, Member Naming sig, Member (Reader Scope) sig, Member (Reader Span) sig) => Carrier (Elab :+: sig) (ElabC m) where
  eff (L (Exists _ k)) = do
    -- FIXME: keep a signature
    ctx <- ElabC ask
    n <- Meta <$> gensym "meta"
    k (pure n Value.$$* (pure . Name . Local <$> Context.vars (ctx :: Context (Type Meta))))
  eff (L (GoalIs ty m k)) = ElabC (local (const ty) (runElabC m)) >>= k
  eff (L (Have (Global n) k)) = ElabC (asks (Scope.lookup   n)) >>= k . fmap (Value.weaken . entryType)
  eff (L (Have (Local  n) k)) = ElabC (asks (Context.lookup n)) >>= k
  eff (L (Bind (n ::: t) m k)) = ElabC (local (Context.insert (n ::: t)) (runElabC m)) >>= k
  eff (L (Unify (tm1 ::: ty1 :===: tm2 ::: ty2) k)) = ElabC $ do
    span <- ask
    context <- ask
    tell (Set.fromList
      [ (context :|-: (ty1 :===: ty2) ::: Value.Type) :~ span
      , (context :|-: (tm1 :===: tm2) ::: ty1)        :~ span
      ])
    runElabC k
  eff (R other) = ElabC (eff (R (R (R (handleCoercible other)))))

runSolver :: ( Carrier sig m
             , Effect sig
             , Member (Error Doc) sig
             , Member Naming sig
             , Member (Reader Scope) sig
             )
          => Set.Set Constraint
          -> Value Meta
          -> m (Value Meta)
runSolver constraints tm = do
  subst <- solver constraints
  pure (apply subst tm)

inferredType :: (Carrier sig m, Member Naming sig) => Maybe (Type Meta) -> m (Type Meta)
inferredType = maybe (pure . Meta <$> gensym "meta") pure


type ModuleTable = Map.Map ModuleName Scope

elabModule :: ( Carrier sig m
              , Effect sig
              , Member (Error Doc) sig
              , Member Naming sig
              , Member (Reader ModuleTable) sig
              , Member (State (Stack Doc)) sig
              , Member (State Scope) sig
              )
           => Module Qualified (Core.Core Name)
           -> m (Module Qualified (Value Name ::: Type Name))
elabModule m = namespace (show (moduleName m)) $ do
  for_ (moduleImports m) (modify . Scope.union <=< importModule)

  decls <- for (moduleDecls m) $ \ decl ->
    (Just <$> elabDecl decl) `catchError` ((Nothing <$) . logError)
  pure m { moduleDecls = catMaybes decls }

logError :: (Member (State (Stack Doc)) sig, Carrier sig m) => Doc -> m ()
logError = modify . flip (:>)

importModule :: ( Carrier sig m
                , Member (Error Doc) sig
                , Member (Reader ModuleTable) sig
                )
             => Import
             -> m Scope
importModule n = asks (Map.lookup (importModuleName n)) >>= maybe (unknownModule n) pure


elabDecl :: ( Carrier sig m
            , Effect sig
            , Member (Error Doc) sig
            , Member Naming sig
            , Member (State Scope) sig
            )
         => Decl Qualified (Core.Core Name)
         -> m (Decl Qualified (Value Name ::: Type Name))
elabDecl decl = namespace (show (declName decl)) . runReader (declSpan decl) $ case decl of
  Declare name ty span -> do
    ty' <- runScope (declare (elab ty))
    modify (Scope.insert name (Decl ty'))
    pure (Declare name (ty' ::: Value.Type) span)
  Define  name tm span -> do
    ty <- gets (fmap Value.weaken . fmap entryType . Scope.lookup name) >>= inferredType
    elab <- runScope (define ty (elab tm))
    modify (Scope.insert name (Defn elab))
    pure (Define name elab span)
  Doc docs     d  span -> Doc docs <$> elabDecl d <*> pure span

declare :: ( Carrier sig m
           , Effect sig
           , Member (Error Doc) sig
           , Member Naming sig
           , Member (Reader Scope) sig
           )
        => ElabC m (Value Meta)
        -> m (Value Name)
declare ty = do
  ty' <- runElab Value.Type ty >>= uncurry runSolver
  pure (Value.generalizeType ty')

define :: ( Carrier sig m
          , Effect sig
          , Member (Error Doc) sig
          , Member Naming sig
          , Member (Reader Scope) sig
          , Member (Reader Span) sig
          )
       => Value Meta
       -> ElabC m (Value Meta)
       -> m (Value Name ::: Type Name)
define ty tm = do
  (constraints, tm') <- runElab ty tm
  subst <- solver constraints
  let ty' = Value.generalizeType (apply subst ty)
  (::: ty') <$> Value.generalizeValue (apply subst tm' ::: ty')

runScope :: (Carrier sig m, Member (State Scope) sig) => ReaderC Scope m a -> m a
runScope m = get >>= flip runReader m
