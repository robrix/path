{-# LANGUAGE DeriveFunctor, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, KindSignatures, MultiParamTypeClasses, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.Elab where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader hiding (Reader(Local))
import Control.Effect.State
import Control.Effect.Writer
import Control.Monad ((<=<))
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
import Path.Module
import Path.Name
import Path.Plicity
import Path.Scope as Scope
import Path.Semiring
import Path.Solver
import Path.Usage
import Path.Value (Type, Value(..))
import qualified Path.Value as Value
import Prelude hiding (pi)
import Text.Trifecta.Rendering (Span(..), Spanned(..))

assume :: ( Carrier sig m
          , Member (Error ElabError) sig
          , Member Naming sig
          , Member (Reader (Context (Type Meta))) sig
          , Member (Reader Scope) sig
          , Member (Reader Span) sig
          , Member (Reader (Type Meta)) sig
          , Member (Writer (Set.Set HetConstraint)) sig
          )
       => Qual
       -> m (Value Meta ::: Type Meta)
assume v = do
  _A <- lookupVar v
  expect (pure (Qual v) ::: _A)

intro :: ( Carrier sig m
         , Member Naming sig
         , Member (Reader (Context (Type Meta))) sig
         , Member (Reader Span) sig
         , Member (Reader (Type Meta)) sig
         , Member (Writer (Set.Set HetConstraint)) sig
         )
      => (Qual -> m (Value Meta ::: Type Meta))
      -> m (Value Meta ::: Type Meta)
intro body = do
  _A ::: _ <- exists Type
  x <- gensym "intro"
  _B ::: _ <- x ::: _A |- exists Type
  u ::: _ <- x ::: _A |- goalIs _B (body (Local x))
  expect (Value.lam (qlocal x) u ::: Value.pi ((qlocal x, Ex, zero) ::: _A) _B)

type' :: ( Carrier sig m
         , Member Naming sig
         , Member (Reader (Context (Type Meta))) sig
         , Member (Reader Span) sig
         , Member (Reader (Type Meta)) sig
         , Member (Writer (Set.Set HetConstraint)) sig
         )
      => m (Value Meta ::: Type Meta)
type' = expect (Type ::: Type)

pi :: ( Carrier sig m
      , Member Naming sig
      , Member (Reader (Context (Type Meta))) sig
      , Member (Reader Span) sig
      , Member (Reader (Type Meta)) sig
      , Member (Writer (Set.Set HetConstraint)) sig
      )
   => Plicity
   -> Usage
   -> m (Value Meta ::: Type Meta)
   -> (Qual -> m (Value Meta ::: Type Meta))
   -> m (Value Meta ::: Type Meta)
pi p m t body = do
  t' ::: _ <- goalIs Type t
  x <- gensym "pi"
  b' ::: _ <- x ::: t' |- goalIs Type (body (Local x))
  expect (Value.pi ((qlocal x, p, m) ::: t') b' ::: Type)

app :: ( Carrier sig m
       , Member Naming sig
       , Member (Reader (Context (Type Meta))) sig
       , Member (Reader Span) sig
       , Member (Reader (Type Meta)) sig
       , Member (Writer (Set.Set HetConstraint)) sig
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
          , Member (Writer (Set.Set HetConstraint)) sig
          )
       => Value Meta ::: Type Meta
       -> m (Value Meta ::: Type Meta)
expect exp = do
  res <- goal >>= exists
  res <$ unify (exp :===: res)

freshName :: ( Carrier sig m
             , Member Naming sig
             )
          => String
          -> m Qual
freshName s = Local <$> gensym s

context :: (Carrier sig m, Member (Reader (Context (Type Meta))) sig) => m (Context (Type Meta))
context = ask

exists :: ( Carrier sig m
          , Member Naming sig
          , Member (Reader (Context (Type Meta))) sig
          )
       => Type Meta
       -> m (Value Meta ::: Type Meta)
exists ty = do
  ctx <- context
  n <- Meta <$> gensym "meta"
  pure (pure n Value.$$* map (pure . qlocal) (toList (Context.vars ctx)) ::: ty)

goal :: (Carrier sig m, Member (Reader (Type Meta)) sig) => m (Type Meta)
goal = ask

goalIs :: (Carrier sig m, Member (Reader (Type Meta)) sig) => Type Meta -> m a -> m a
goalIs ty = local (const ty)

unify :: ( Carrier sig m
         , Member (Reader (Context (Type Meta))) sig
         , Member (Reader Span) sig
         , Member (Writer (Set.Set HetConstraint)) sig
         )
      => Equation (Value Meta ::: Type Meta)
      -> m ()
unify constraint = (:~) <$> asks (:|-: constraint) <*> ask >>= tell . Set.singleton


elab :: ( Carrier sig m
        , Member (Error ElabError) sig
        , Member Naming sig
        , Member (Reader (Context (Type Meta))) sig
        , Member (Reader Scope) sig
        , Member (Reader Span) sig
        , Member (Reader (Type Meta)) sig
        , Member (Writer (Set.Set HetConstraint)) sig
        )
     => Core.Core Qual
     -> m (Value Meta ::: Type Meta)
elab = \case
  Core.Var n -> assume n
  Core.Lam b -> intro (\ n -> elab (Core.instantiate (pure n) b))
  f Core.:$ a -> app (elab f) (elab a)
  Core.Type -> type'
  Core.Pi p m t b -> pi p m (elab t) (\ n -> elab (Core.instantiate (pure n) b))
  Core.Hole _ -> goal >>= exists
  Core.Ann ann b -> local (const ann) (elab b)


runSolver :: ( Carrier sig m
             , Effect sig
             , Member (Error SolverError) sig
             , Member Naming sig
             , Member (Reader Scope) sig
             )
          => Set.Set HetConstraint
          -> Value Meta ::: Type Meta
          -> m (Value Meta ::: Type Meta)
runSolver constraints (tm ::: ty) = do
  subst <- solver (foldMap hetToHom constraints)
  pure (apply subst tm ::: apply subst ty)

runElab :: ( Carrier sig m
           , Effect sig
           , Member Naming sig
           )
        => Maybe (Type Meta)
        -> ReaderC Span (ReaderC (Type Meta) (ReaderC (Context (Type Meta)) (WriterC (Set.Set HetConstraint) m))) (Value Meta ::: Type Meta)
        -> m (Set.Set HetConstraint, Value Meta ::: Type Meta)
runElab ty m = do
  ty' <- maybe (pure . Meta <$> gensym "meta") pure ty
  runWriter . runReader mempty . runReader ty' . runReader (Span mempty mempty mempty) $ do
    val <- exists ty'
    m' <- m
    m' <$ unify (m' :===: val)


(|-) :: (Carrier sig m, Member (Reader (Context (Type Meta))) sig) => Gensym ::: Type Meta -> m a -> m a
n ::: t |- m = local (Context.insert (n ::: t)) m

infix 5 |-

throwElabError :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader (Context (Type Meta))) sig, Member (Reader Span) sig) => ErrorReason -> m a
throwElabError reason = ElabError <$> ask <*> ask <*> pure reason >>= throwError

lookupVar :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader (Context (Type Meta))) sig, Member (Reader Scope) sig, Member (Reader Span) sig) => Qual -> m (Type Meta)
lookupVar (Global n) = asks (Scope.lookup (Global n)) >>= maybe (throwElabError (FreeVariable (Global n))) (pure . entryType)
lookupVar (Local  n) = asks (Context.lookup n)        >>= maybe (throwElabError (FreeVariable (Local n))) pure


type ModuleTable = Map.Map ModuleName Scope

elabModule :: ( Carrier sig m
              , Effect sig
              , Member (Error ModuleError) sig
              , Member Naming sig
              , Member (Reader ModuleTable) sig
              , Member (State (Stack ElabError)) sig
              , Member (State (Stack SolverError)) sig
              , Member (State Scope) sig
              )
           => Module Qual (Core.Core Qual)
           -> m (Module Qual (Value Meta ::: Type Meta))
elabModule m = namespace (show (moduleName m)) $ do
  for_ (moduleImports m) (modify . Scope.union <=< importModule)

  decls <- for (moduleDecls m) (either ((Nothing <$) . logElabError) (either ((Nothing <$) . logSolverError) (pure . Just)) <=< runError . runError . elabDecl)
  pure m { moduleDecls = catMaybes decls }

logElabError :: (Carrier sig m, Member (State (Stack ElabError)) sig) => ElabError -> m ()
logElabError = modify . flip (:>)

logSolverError :: (Carrier sig m, Member (State (Stack SolverError)) sig) => SolverError -> m ()
logSolverError = modify . flip (:>)

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
            , Member (Error SolverError) sig
            , Member Naming sig
            , Member (State Scope) sig
            )
         => Decl Qual (Core.Core Qual)
         -> m (Decl Qual (Value Meta ::: Type Meta))
elabDecl = namespace . show . declName <*> \case
  Declare name ty -> Declare name <$> elabDeclare name ty
  Define  name tm -> Define  name <$> elabDefine  name tm
  Doc docs     d  -> Doc docs <$> elabDecl d

elabDeclare :: ( Carrier sig m
               , Effect sig
               , Member (Error ElabError) sig
               , Member (Error SolverError) sig
               , Member Naming sig
               , Member (State Scope) sig
               )
            => Qual
            -> Core.Core Qual
            -> m (Value Meta ::: Type Meta)
elabDeclare name ty = do
  elab <- runScope (runElab (Just Value.Type) (elab ty) >>= uncurry runSolver)
  elab <$ modify (Scope.insert name (Decl (Value.generalizeType (typedTerm elab))))

elabDefine :: ( Carrier sig m
              , Effect sig
              , Member (Error ElabError) sig
              , Member (Error SolverError) sig
              , Member Naming sig
              , Member (State Scope) sig
              )
           => Qual
           -> Core.Core Qual
           -> m (Value Meta ::: Type Meta)
elabDefine name tm = do
  ty <- gets (fmap entryType . Scope.lookup name)
  (constraints, res) <- runScope . runElab ty $ do
    ty' <- maybe (typedTerm <$> exists Type) pure ty
    val <- exists ty'
    modify (Scope.insert name (Defn val))
    m' <- elab tm
    m' <$ unify (m' :===: val)
  tm ::: ty <- runScope (runSolver constraints res)
  tm' <- Value.generalizeValue (tm ::: ty)
  (tm' ::: ty) <$ modify (Scope.insert name (Defn (tm' ::: ty)))

runScope :: (Carrier sig m, Member (State Scope) sig) => ReaderC Scope m a -> m a
runScope m = get >>= flip runReader m
