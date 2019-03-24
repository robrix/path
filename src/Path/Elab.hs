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

assume :: ( Carrier sig m
          , Member (Error Doc) sig
          , Member Naming sig
          , Member (Reader (Context (Type Meta))) sig
          , Member (Reader Scope) sig
          , Member (Reader Span) sig
          , Member (Reader (Type Meta)) sig
          , Member (Writer (Set.Set Constraint)) sig
          )
       => Name
       -> m (Value Meta ::: Type Meta)
assume v = do
  _A <- have v
  expect (pure (Name v) ::: _A)

intro :: ( Carrier sig m
         , Member Naming sig
         , Member (Reader (Context (Type Meta))) sig
         , Member (Reader Span) sig
         , Member (Reader (Type Meta)) sig
         , Member (Writer (Set.Set Constraint)) sig
         )
      => Maybe User
      -> (Name -> m (Value Meta ::: Type Meta))
      -> m (Value Meta ::: Type Meta)
intro x body = do
  _A ::: _ <- exists Type
  x <- gensym (maybe "_" showUser x)
  _B ::: _ <- x ::: _A |- exists Type
  u ::: _ <- x ::: _A |- goalIs _B (body (Local x))
  expect (Value.lam (Name (Local x)) u ::: Value.pi ((Name (Local x), Ex, zero) ::: _A) _B)

type' :: ( Carrier sig m
         , Member Naming sig
         , Member (Reader (Context (Type Meta))) sig
         , Member (Reader Span) sig
         , Member (Reader (Type Meta)) sig
         , Member (Writer (Set.Set Constraint)) sig
         )
      => m (Value Meta ::: Type Meta)
type' = expect (Type ::: Type)

pi :: ( Carrier sig m
      , Member Naming sig
      , Member (Reader (Context (Type Meta))) sig
      , Member (Reader Span) sig
      , Member (Reader (Type Meta)) sig
      , Member (Writer (Set.Set Constraint)) sig
      )
   => Maybe User
   -> Plicity
   -> Usage
   -> m (Value Meta ::: Type Meta)
   -> (Name -> m (Value Meta ::: Type Meta))
   -> m (Value Meta ::: Type Meta)
pi x p m t body = do
  t' ::: _ <- goalIs Type t
  x <- gensym (maybe "_" showUser x)
  b' ::: _ <- x ::: t' |- goalIs Type (body (Local x))
  expect (Value.pi ((qlocal x, p, m) ::: t') b' ::: Type)

app :: ( Carrier sig m
       , Member Naming sig
       , Member (Reader (Context (Type Meta))) sig
       , Member (Reader Span) sig
       , Member (Reader (Type Meta)) sig
       , Member (Writer (Set.Set Constraint)) sig
       )
    => m (Value Meta ::: Type Meta)
    -> m (Value Meta ::: Type Meta)
    -> m (Value Meta ::: Type Meta)
app f a = do
  _A ::: _ <- exists Type
  _B ::: _ <- exists Type
  x <- gensym "app"
  f' ::: _ <- goalIs (Value.pi ((qlocal x, Ex, zero) ::: _A) _B) f
  a' ::: _ <- goalIs _A a
  expect (f' Value.$$ a' ::: _B)


expect :: ( Carrier sig m
          , Member Naming sig
          , Member (Reader (Context (Type Meta))) sig
          , Member (Reader Span) sig
          , Member (Reader (Type Meta)) sig
          , Member (Writer (Set.Set Constraint)) sig
          )
       => Value Meta ::: Type Meta
       -> m (Value Meta ::: Type Meta)
expect exp = do
  res <- goal >>= exists
  res <$ unify (exp :===: res)

exists :: ( Carrier sig m
          , Member Naming sig
          , Member (Reader (Context (Type Meta))) sig
          )
       => Type Meta
       -> m (Value Meta ::: Type Meta)
exists ty = do
  ctx <- ask
  n <- Meta <$> gensym "meta"
  pure (pure n Value.$$* (pure . Name . Local <$> Context.vars (ctx :: Context (Type Meta))) ::: ty)

goal :: (Carrier sig m, Member (Reader (Type Meta)) sig) => m (Type Meta)
goal = ask

goalIs :: (Carrier sig m, Member (Reader (Type Meta)) sig) => Type Meta -> m a -> m a
goalIs ty = local (const ty)

unify :: ( Carrier sig m
         , Member (Reader (Context (Type Meta))) sig
         , Member (Reader Span) sig
         , Member (Writer (Set.Set Constraint)) sig
         )
      => Equation (Value Meta ::: Type Meta)
      -> m ()
unify (tm1 ::: ty1 :===: tm2 ::: ty2) = do
  span <- ask
  context <- ask
  tell (Set.fromList
    [ (context :|-: (ty1 :===: ty2) ::: Value.Type) :~ span
    , (context :|-: (tm1 :===: tm2) ::: ty1)        :~ span
    ])

spanIs :: (Carrier sig m, Member (Reader Span) sig) => Span -> m a -> m a
spanIs span = local (const span)


elab :: ( Carrier sig m
        , Member (Error Doc) sig
        , Member Naming sig
        , Member (Reader (Context (Type Meta))) sig
        , Member (Reader Scope) sig
        , Member (Reader Span) sig
        , Member (Reader (Type Meta)) sig
        , Member (Writer (Set.Set Constraint)) sig
        )
     => Core.Core Name
     -> m (Value Meta ::: Type Meta)
elab = \case
  Core.Var n -> assume n
  Core.Lam n b -> intro n (\ n' -> elab (Core.instantiate (pure n') b))
  f Core.:$ a -> app (elab f) (elab a)
  Core.Type -> type'
  Core.Pi n p m t b -> pi n p m (elab t) (\ n' -> elab (Core.instantiate (pure n') b))
  Core.Hole _ -> goal >>= exists
  Core.Ann ann b -> spanIs ann (elab b)


data Elab m k
  = Exists (Type Meta) (Value Meta ::: Type Meta -> k)
  | Goal (Type Meta -> k)
  | forall a . GoalIs (Type Meta) (m a) (a -> k)
  | Have Name (Type Meta -> k)
  | forall a . Bind (Gensym ::: Type Meta) (m a) (a -> k)
  | Unify (Equation (Value Meta ::: Type Meta)) k
  | forall a . SpanIs Span (m a) (a -> k)

deriving instance Functor (Elab m)

instance HFunctor Elab where
  hmap f = \case
    Exists t   k -> Exists t       k
    Goal       k -> Goal           k
    GoalIs t m k -> GoalIs t (f m) k
    Have   n   k -> Have   n       k
    Bind   b m k -> Bind   b (f m) k
    Unify  q   k -> Unify  q       k
    SpanIs s m k -> SpanIs s (f m) k

instance Effect Elab where
  handle state handler = \case
    Exists t   k -> Exists t                        (handler . (<$ state) . k)
    Goal       k -> Goal                            (handler . (<$ state) . k)
    GoalIs t m k -> GoalIs t (handler (m <$ state)) (handler . fmap k)
    Have   n   k -> Have   n                        (handler . (<$ state) . k)
    Bind   b m k -> Bind   b (handler (m <$ state)) (handler . fmap k)
    Unify  q   k -> Unify  q                        (handler (k <$ state))
    SpanIs s m k -> SpanIs s (handler (m <$ state)) (handler . fmap k)


newtype ElabC m a = ElabC { runElabC :: ReaderC (Type Meta) (ReaderC (Context (Type Meta)) (WriterC (Set.Set Constraint) m)) a }
  deriving (Applicative, Functor, Monad)

instance (Carrier sig m, Effect sig, Member (Error Doc) sig, Member Naming sig, Member (Reader Scope) sig, Member (Reader Span) sig) => Carrier (Elab :+: sig) (ElabC m) where
  eff (L (Exists ty k)) = do
    ctx <- ElabC ask
    n <- Meta <$> gensym "meta"
    k (pure n Value.$$* (pure . Name . Local <$> Context.vars (ctx :: Context (Type Meta))) ::: ty)
  eff (L (Goal k)) = ElabC ask >>= k
  eff (L (GoalIs ty m k)) = ElabC (local (const ty) (runElabC m)) >>= k
  eff (L (Have (Global n) k)) = ElabC (asks (Scope.lookup   n)) >>= maybe (freeVariable (Global n)) (k . Value.weaken . entryType)
  eff (L (Have (Local  n) k)) = ElabC (asks (Context.lookup n)) >>= maybe (freeVariable (Local  n)) k
  eff (L (Bind (n ::: t) m k)) = ElabC (local (Context.insert (n ::: t)) (runElabC m)) >>= k
  eff (L (Unify (tm1 ::: ty1 :===: tm2 ::: ty2) k)) = ElabC $ do
    span <- ask
    context <- ask
    tell (Set.fromList
      [ (context :|-: (ty1 :===: ty2) ::: Value.Type) :~ span
      , (context :|-: (tm1 :===: tm2) ::: ty1)        :~ span
      ])
    runElabC k
  eff (L (SpanIs s m k)) = ElabC (local (const s) (runElabC m)) >>= k
  eff (R other) = ElabC (eff (R (R (R (handleCoercible other)))))


runSolver :: ( Carrier sig m
             , Effect sig
             , Member (Error Doc) sig
             , Member Naming sig
             , Member (Reader Scope) sig
             )
          => Set.Set Constraint
          -> Value Meta ::: Type Meta
          -> m (Value Meta ::: Type Meta)
runSolver constraints (tm ::: ty) = do
  subst <- solver constraints
  pure (apply subst tm ::: apply subst ty)

runElab :: Type Meta
        -> ReaderC (Type Meta) (ReaderC (Context (Type Meta)) (WriterC (Set.Set Constraint) m)) (Value Meta ::: Type Meta)
        -> m (Set.Set Constraint, Value Meta ::: Type Meta)
runElab ty m = runWriter (runReader mempty (runReader ty m))

inferredType :: (Carrier sig m, Member Naming sig) => Maybe (Type Meta) -> m (Type Meta)
inferredType = maybe (pure . Meta <$> gensym "meta") pure


(|-) :: (Carrier sig m, Member (Reader (Context (Type Meta))) sig) => Gensym ::: Type Meta -> m a -> m a
n ::: t |- m = local (Context.insert (n ::: t)) m

infix 5 |-

have :: (Carrier sig m, Member (Error Doc) sig, Member (Reader (Context (Type Meta))) sig, Member (Reader Scope) sig, Member (Reader Span) sig) => Name -> m (Type Meta)
have (Global n) = asks (Scope.lookup   n) >>= maybe (freeVariable (Global n)) (pure . Value.weaken . entryType)
have (Local  n) = asks (Context.lookup n) >>= maybe (freeVariable (Local  n)) pure


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
  Declare name ty span -> Declare name <$> elabDeclare name ty <*> pure span
  Define  name tm span -> Define  name <$> elabDefine  name tm <*> pure span
  Doc docs     d  span -> Doc docs <$> elabDecl d <*> pure span

elabDeclare :: ( Carrier sig m
               , Effect sig
               , Member (Error Doc) sig
               , Member Naming sig
               , Member (Reader Span) sig
               , Member (State Scope) sig
               )
            => Qualified
            -> Core.Core Name
            -> m (Value Name ::: Type Name)
elabDeclare name ty = do
  tm ::: ty <- runScope (runElab Value.Type (elab ty) >>= uncurry runSolver)
  let elab = (Value.generalizeType tm ::: Value.generalizeType ty)
  elab <$ modify (Scope.insert name (Decl (typedTerm elab)))

elabDefine :: ( Carrier sig m
              , Effect sig
              , Member (Error Doc) sig
              , Member Naming sig
              , Member (Reader Span) sig
              , Member (State Scope) sig
              )
           => Qualified
           -> Core.Core Name
           -> m (Value Name ::: Type Name)
elabDefine name tm = do
  ty <- gets (fmap Value.weaken . fmap entryType . Scope.lookup name) >>= inferredType
  (constraints, res) <- runScope (runElab ty (elab tm))
  tm ::: ty <- runScope (runSolver constraints res)
  let ty' = Value.generalizeType ty
  tm' <- Value.generalizeValue (tm ::: ty')
  (tm' ::: ty') <$ modify (Scope.insert name (Defn (tm' ::: ty')))

runScope :: (Carrier sig m, Member (State Scope) sig) => ReaderC Scope m a -> m a
runScope m = get >>= flip runReader m
