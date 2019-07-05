{-# LANGUAGE FlexibleContexts, LambdaCase, TypeApplications, TypeOperators #-}
module Path.Elab where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader hiding (Reader(Local))
import Control.Effect.State
import Control.Effect.Writer
import Control.Monad ((<=<))
import Data.Bifunctor (first)
import Data.Foldable (for_)
import Data.Functor.Const
import Data.List (elemIndex)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (catMaybes)
import Data.Traversable (for)
import Path.Stack as Stack
import Path.Constraint hiding ((|-))
import Path.Context as Context
import Path.Core
import Path.Error
import Path.Module
import Path.Name
import Path.Namespace as Namespace
import Path.Plicity
import Path.Pretty
import Path.Scope
import Path.Semiring
import Path.Solver
import Path.Span
import qualified Path.Surface as Surface
import Path.Usage
import Prelude hiding (pi)

assume :: ( Carrier sig m
          , Member (Error Doc) sig
          , Member (Reader Namespace) sig
          , Member (Reader Span) sig
          )
       => Qualified
       -> m (Core (Name Meta) ::: Core (Name Meta))
assume n = asks (fmap (weaken . entryType) . Namespace.lookup n) >>= maybe (freeVariable n) (pure . (global n :::))

intro :: ( Carrier sig m
         , Member Naming sig
         , Member (Reader (Context (Core (Name Meta)))) sig
         , Member (Reader Span) sig
         , Member (State Signature) sig
         , Member (Writer (Set.Set (Spanned (Constraint Core (Name Meta))))) sig
         )
      => Plicit (Maybe User)
      -> m (Core (Name Meta) ::: Core (Name Meta))
      -> m (Core (Name Meta) ::: Core (Name Meta))
intro (p :< _) body = do
  _A <- exists Type
  x <- fresh
  _B <- x ::: _A |- exists Type
  u <- x ::: _A |- goalIs _B body
  pure (lam (p :< Local (Name x)) u ::: pi (p :< Local (Name x) ::: More :@ _A) _B)

(-->) :: ( Carrier sig m
         , Member Naming sig
         , Member (Reader (Context (Core (Name Meta)))) sig
         , Member (Reader Span) sig
         , Member (State Signature) sig
         , Member (Writer (Set.Set (Spanned (Constraint Core (Name Meta))))) sig
         )
      => Plicit (Maybe User, Used (m (Core (Name Meta) ::: Core (Name Meta))))
      -> m (Core (Name Meta) ::: Core (Name Meta))
      -> m (Core (Name Meta) ::: Core (Name Meta))
(p :< (_, m :@ t)) --> body = do
  t' <- goalIs Type t
  x <- fresh
  b' <- x ::: t' |- goalIs Type body
  pure (pi (p :< Local (Name x) ::: m :@ t') b' ::: Type)

app :: ( Carrier sig m
       , Member Naming sig
       , Member (Reader (Context (Core (Name Meta)))) sig
       , Member (Reader Span) sig
       , Member (State Signature) sig
       , Member (Writer (Set.Set (Spanned (Constraint Core (Name Meta))))) sig
       )
    => m (Core (Name Meta) ::: Core (Name Meta))
    -> Plicit (m (Core (Name Meta) ::: Core (Name Meta)))
    -> m (Core (Name Meta) ::: Core (Name Meta))
app f (p :< a) = do
  _A <- exists Type
  x <- fresh
  _B <- x ::: _A |- exists Type
  let _F = pi (p :< Local (Name x) ::: case p of { Im -> zero ; Ex -> More } :@ _A) _B
  f' <- goalIs _F f
  a' <- goalIs _A a
  pure (f' $$ (p :< a') ::: _F $$ (p :< a'))


exists :: ( Carrier sig m
          , Member Naming sig
          , Member (Reader (Context (Core (Name Meta)))) sig
          , Member (State Signature) sig
          )
       => Core (Name Meta)
       -> m (Core (Name Meta))
exists ty = do
  ctx <- ask
  n <- fresh
  let f (n ::: t) = Ex :< Local (Name n) ::: More :@ t
      ty' = pis (f <$> Context.unContext ctx) ty
  modify (Signature . Map.insert n ty' . unSignature)
  pure (pure (Local (Meta n)) $$* ((Ex :<) . pure . Local . Name <$> Context.vars (ctx :: Context (Core (Name Meta)))))

goalIs :: ( Carrier sig m
          , Member Naming sig
          , Member (Reader (Context (Core (Name Meta)))) sig
          , Member (Reader Span) sig
          , Member (State Signature) sig
          , Member (Writer (Set.Set (Spanned (Constraint Core (Name Meta))))) sig
          )
       => Core (Name Meta)
       -> m (Core (Name Meta) ::: Core (Name Meta))
       -> m (Core (Name Meta))
goalIs ty2 m = do
  tm1 ::: ty1 <- m
  tm2 <- exists ty2
  tm2 <$ unify (tm1 ::: ty1 :===: tm2 ::: ty2)

unify :: (Carrier sig m, Member (Reader (Context (Core (Name Meta)))) sig, Member (Reader Span) sig, Member (Writer (Set.Set (Spanned (Constraint Core (Name Meta))))) sig)
      => Equation (Core (Name Meta) ::: Core (Name Meta))
      -> m ()
unify (tm1 ::: ty1 :===: tm2 ::: ty2) = do
  span <- ask
  context <- asks (fmap (first (Local . Name)) . unContext)
  tell (Set.fromList
    [ binds context ((ty1 :===: ty2) ::: Type) :~ span
    , binds context ((tm1 :===: tm2) ::: ty1)  :~ span
    ])

(|-) :: (Carrier sig m, Member (Reader (Context (Core (Name Meta)))) sig) => Gensym ::: Core (Name Meta) -> m a -> m a
b |- m = local (Context.insert b) m

infix 5 |-


spanIs :: (Carrier sig m, Member (Reader Span) sig) => Span -> m a -> m a
spanIs span = local (const span)

elab :: ( Carrier sig m
        , Member (Error Doc) sig
        , Member Naming sig
        , Member (Reader (Context (Core (Name Meta)))) sig
        , Member (Reader Namespace) sig
        , Member (Reader Span) sig
        , Member (State Signature) sig
        , Member (Writer (Set.Set (Spanned (Constraint Core (Name Meta))))) sig
        )
     => Surface.Surface Qualified
     -> m (Core (Name Meta) ::: Core (Name Meta))
elab = Surface.kcata id alg bound assume
  where bound (Z _) = asks @(Context (Core (Name Meta))) (first (pure . Local . Name) . Stack.head . unContext)
        bound (S m) = local @(Context (Core (Name Meta))) (Context . Stack.tail . unContext) m
        alg = \case
          Surface.Lam n b -> intro (unIgnored <$> n) (elab' (unScope <$> b))
          (f Surface.:$ (p :< a)) -> app (elab' f) (p :< elab' a)
          Surface.Type -> pure (Type ::: Type)
          Surface.Pi (p :< Ignored n ::: t) b -> (p :< (n, elab' <$> t)) --> elab' (unScope <$> b)
        elab' (t :~ s) = spanIs s (getConst t)

type ElabC m = ReaderC (Context (Core (Name Meta))) (WriterC (Set.Set (Spanned (Constraint Core (Name Meta)))) m)

runElab :: ElabC m a -> m (Set.Set (Spanned (Constraint Core (Name Meta))), a)
runElab = runWriter . runReader mempty


inferType :: (Carrier sig m, Member Naming sig) => m (Core (Name Meta))
inferType = pure . Local . Meta <$> fresh


type ModuleTable = Map.Map ModuleName Namespace

elabModule :: ( Carrier sig m
              , Effect sig
              , Member (Error Doc) sig
              , Member Naming sig
              , Member (Reader ModuleTable) sig
              , Member (State (Stack Doc)) sig
              , Member (State Namespace) sig
              )
           => Module Surface.Surface Qualified
           -> m (Module Core Qualified)
elabModule m = namespace (show (moduleName m)) . runReader (moduleName m) $ do
  for_ (moduleImports m) (modify . Namespace.union <=< importModule)

  decls <- for (moduleDecls m) $ \ decl ->
    (Just . fmap (bind (`elemIndex` map qualified (moduleDecls m))) <$> elabDecl (instantiate (pure . qualified . (moduleDecls m !!)) <$> decl)) `catchError` ((Nothing <$) . logError)
  pure m { moduleDecls = catMaybes decls }
  where qualified = (moduleName m :.:) . declName

logError :: (Member (State (Stack Doc)) sig, Carrier sig m) => Doc -> m ()
logError = modify . flip (:>)

importModule :: ( Carrier sig m
                , Member (Error Doc) sig
                , Member (Reader ModuleTable) sig
                )
             => Spanned Import
             -> m Namespace
importModule n@(i :~ _) = asks (Map.lookup (importModuleName i)) >>= maybe (unknownModule n) pure


elabDecl :: ( Carrier sig m
            , Effect sig
            , Member (Error Doc) sig
            , Member Naming sig
            , Member (Reader ModuleName) sig
            , Member (State Namespace) sig
            )
         => Decl (Surface.Surface Qualified)
         -> m (Decl (Core Qualified))
elabDecl (Decl name d tm ty) = namespace (show name) $ do
  ty' <- runSpanned (runNamespace . declare . elab) ty
  moduleName <- ask
  modify (Namespace.insert (moduleName :.: name) (Entry (Nothing ::: unSpanned ty')))
  (tm' ::: _) :~ s <- runSpanned (runNamespace . define (weaken (unSpanned ty')) . elab) tm
  modify (Namespace.insert (moduleName :.: name) (Entry (Just tm' ::: unSpanned ty')))
  pure (Decl name d (tm' :~ s) ty')

declare :: ( Carrier sig m
           , Effect sig
           , Member (Error Doc) sig
           , Member Naming sig
           , Member (Reader Namespace) sig
           , Member (Reader Span) sig
           )
        => ElabC (StateC Signature m) (Core (Name Meta) ::: Core (Name Meta))
        -> m (Core Qualified)
declare ty = evalState (mempty :: Signature) $ do
  (constraints, ty') <- runElab (goalIs Type ty)
  subst <- solver constraints
  pure (generalizeType (apply subst ty'))

define :: ( Carrier sig m
          , Effect sig
          , Member (Error Doc) sig
          , Member Naming sig
          , Member (Reader Namespace) sig
          , Member (Reader Span) sig
          )
       => Core (Name Meta)
       -> ElabC (StateC Signature m) (Core (Name Meta) ::: Core (Name Meta))
       -> m (Core Qualified ::: Core Qualified)
define ty tm = evalState (mempty :: Signature) $ do
  (constraints, tm') <- runElab (goalIs ty tm)
  subst <- solver constraints
  let ty' = generalizeType (apply subst ty)
  (::: ty') <$> strengthen (apply subst tm')

runNamespace :: (Carrier sig m, Member (State Namespace) sig) => ReaderC Namespace m a -> m a
runNamespace m = get >>= flip runReader m
