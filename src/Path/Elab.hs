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
import Data.Foldable (foldl', for_)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (catMaybes)
import Data.Traversable (for)
import Path.Stack as Stack
import Path.Constraint hiding ((|-))
import Path.Context as Context
import Path.Core (Type, Core(..))
import qualified Path.Core as Core
-- import Path.Eval
import Path.Module
import Path.Name
import Path.Plicity
import Path.Pretty
import Path.Namespace as Namespace
import Path.Semiring
import Path.Solver
import qualified Path.Surface as Surface
import Path.Usage
import Prelude hiding (pi)
import Text.Trifecta.Rendering (Span(..), Spanned(..))

assume :: (Carrier sig m, Member Elab sig, Member Naming sig)
       => Name Gensym
       -> m (Core (Name Meta) ::: Type (Name Meta))
assume v = do
  _A <- have v
  implicits _A >>= foldl' app (pure (name (pure . Local . Name) Core.global v ::: _A))

implicits :: (Carrier sig m, Member Elab sig) => Type (Name Meta) -> m (Stack (Plicit (m (Core (Name Meta) ::: Type (Name Meta)))))
implicits = go Nil
  where go names (Core.Pi (Im :< _ :@ t) b) | False = do
          v <- exists t
          go (names :> (Im :< pure (v ::: t))) (instantiate v b)
        go names _ = pure names

intro :: (Carrier sig m, Member Elab sig, Member Naming sig)
      => Plicit (Maybe User)
      -> (Gensym -> m (Core (Name Meta) ::: Type (Name Meta)))
      -> m (Core (Name Meta) ::: Type (Name Meta))
intro (p :< x) body = do
  _A <- exists Core.Type
  x <- gensym (maybe "intro" showUser x)
  _B <- x ::: _A |- exists Core.Type
  u <- x ::: _A |- goalIs _B (body x)
  pure (Core.lam (p :< Local (Name x)) u ::: Core.pi (p :< Local (Name x) ::: More :@ _A) _B)

pi :: (Carrier sig m, Member Elab sig, Member Naming sig)
   => Plicit (Maybe User, Usage, m (Core (Name Meta) ::: Type (Name Meta)))
   -> (Gensym -> m (Core (Name Meta) ::: Type (Name Meta)))
   -> m (Core (Name Meta) ::: Type (Name Meta))
pi (p :< (x, m, t)) body = do
  t' <- goalIs Core.Type t
  x <- gensym (maybe "pi" showUser x)
  b' <- x ::: t' |- goalIs Core.Type (body x)
  pure (Core.pi (p :< Local (Name x) ::: m :@ t') b' ::: Core.Type)

app :: (Carrier sig m, Member Elab sig, Member Naming sig)
    => m (Core (Name Meta) ::: Type (Name Meta))
    -> Plicit (m (Core (Name Meta) ::: Type (Name Meta)))
    -> m (Core (Name Meta) ::: Type (Name Meta))
app f (p :< a) = do
  _A <- exists Core.Type
  x <- gensym "app"
  _B <- x ::: _A |- exists Core.Type
  let _F = Core.pi (p :< Local (Name x) ::: case p of { Im -> zero ; Ex -> More } :@ _A) _B
  f' <- goalIs _F f
  a' <- goalIs _A a
  pure (f' Core.$$ (p :< a') ::: _F Core.$$ (p :< a'))


exists :: (Carrier sig m, Member Elab sig)
       => Type (Name Meta)
       -> m (Core (Name Meta))
exists ty = send (Exists ty pure)

goalIs :: (Carrier sig m, Member Elab sig) => Type (Name Meta) -> m (Core (Name Meta) ::: Type (Name Meta)) -> m (Core (Name Meta))
goalIs ty2 m = do
  tm1 ::: ty1 <- m
  tm2 <- exists ty2
  tm2 <$ unify (tm1 ::: ty1 :===: tm2 ::: ty2)

unify :: (Carrier sig m, Member Elab sig)
      => Equation (Core (Name Meta) ::: Type (Name Meta))
      -> m ()
unify q = send (Unify q (pure ()))

(|-) :: (Carrier sig m, Member Elab sig) => Gensym ::: Type (Name Meta) -> m a -> m a
b |- m = send (Bind b m pure)

infix 5 |-

have :: (Carrier sig m, Member Elab sig) => Name Gensym -> m (Type (Name Meta))
have n = send (Have n pure)


spanIs :: (Carrier sig m, Member (Reader Span) sig) => Span -> m a -> m a
spanIs span = local (const span)

elab :: (Carrier sig m, Member Elab sig, Member Naming sig, Member (Reader Span) sig)
     => Surface.Surface (Name Meta)
     -> m (Core (Name Meta) ::: Type (Name Meta))
elab = \case
  Surface.Var (Global n) -> assume (Global n)
  Surface.Var (Local (Name n)) -> assume (Local n)
  Surface.Var (Local (Meta n)) -> (pure (Local (Meta n)) :::) <$> exists Core.Type
  Surface.Surface c -> case c of
    Surface.Lam n b -> intro n (\ n' -> elab' (instantiate (pure (Local (Name n'))) <$> b))
    (f Surface.:$ (p :< a)) -> app (elab' f) (p :< elab' a)
    Surface.Type -> pure (Core.Type ::: Core.Type)
    Surface.Pi (p :< n ::: m :@ t) b -> pi (p :< (n, m, elab' t)) (\ n' -> elab' (instantiate (pure (Local (Name n'))) <$> b))
  where elab' (t :~ s) = spanIs s (elab t)


data Elab m k
  = Exists (Type (Name Meta)) (Core (Name Meta) -> k)
  | Have (Name Gensym) (Type (Name Meta) -> k)
  | forall a . Bind (Gensym ::: Type (Name Meta)) (m a) (a -> k)
  | Unify (Equation (Core (Name Meta) ::: Type (Name Meta))) k

deriving instance Functor (Elab m)

instance HFunctor Elab where
  hmap f = \case
    Exists t   k -> Exists t       k
    Have   n   k -> Have   n       k
    Bind   b m k -> Bind   b (f m) k
    Unify  q   k -> Unify  q       k

instance Effect Elab where
  handle state handler = \case
    Exists t   k -> Exists t                        (handler . (<$ state) . k)
    Have   n   k -> Have   n                        (handler . (<$ state) . k)
    Bind   b m k -> Bind   b (handler (m <$ state)) (handler . fmap k)
    Unify  q   k -> Unify  q                        (handler (k <$ state))


runElab :: ElabC m a -> m (Set.Set (Spanned (Constraint (Name Meta))), a)
runElab = runWriter . runReader mempty . runElabC

newtype ElabC m a = ElabC { runElabC :: ReaderC (Context (Type (Name Meta))) (WriterC (Set.Set (Spanned (Constraint (Name Meta)))) m) a }
  deriving (Applicative, Functor, Monad)

instance (Carrier sig m, Effect sig, Member Naming sig, Member (Reader Namespace) sig, Member (Reader Span) sig, Member (State Signature) sig) => Carrier (Elab :+: sig) (ElabC m) where
  eff (L (Exists ty k)) = do
    ctx <- ElabC ask
    n <- gensym "meta"
    let f (n ::: t) = Ex :< Local (Name n) ::: More :@ t
        ty' = Core.pis (f <$> Context.unContext ctx) ty
    modify (Signature . Map.insert n ty' . unSignature)
    k (pure (Local (Meta n)) Core.$$* ((Ex :<) . pure . Local . Name <$> Context.vars (ctx :: Context (Type (Name Meta)))))
  eff (L (Have n k)) = lookup n >>= maybe missing pure >>= k
    where lookup (Global n) = ElabC (asks (Namespace.lookup   n)) >>= pure . fmap (Core.weaken . entryType)
          lookup (Local  n) = ElabC (asks (Context.lookup n))
          missing = do
            ty <- exists Core.Type
            tm <- exists ty
            ty <$ unify (tm ::: ty :===: name (pure . Local . Name) Core.global n ::: ty)
  eff (L (Bind (n ::: t) m k)) = ElabC (local (Context.insert (n ::: t)) (runElabC m)) >>= k
  eff (L (Unify (tm1 ::: ty1 :===: tm2 ::: ty2) k)) = ElabC $ do
    span <- ask
    context <- ask
    tell (Set.fromList
      [ (binds context ((ty1 :===: ty2) ::: Core.Type)) :~ span
      , (binds context ((tm1 :===: tm2) ::: ty1))        :~ span
      ])
    runElabC k
  eff (R other) = ElabC (eff (R (R (handleCoercible other))))

inferType :: (Carrier sig m, Member Naming sig) => m (Type (Name Meta))
inferType = pure . Local . Meta <$> gensym "meta"


type ModuleTable = Map.Map ModuleName Namespace

elabModule :: ( Carrier sig m
              , Effect sig
              , Member (Error Doc) sig
              , Member Naming sig
              , Member (Reader ModuleTable) sig
              , Member (State (Stack Doc)) sig
              , Member (State Namespace) sig
              )
           => Module Qualified (Surface.Surface (Name Meta) ::: Surface.Surface (Name Meta))
           -> m (Module Qualified (Core Qualified ::: Type Qualified))
elabModule m = namespace (show (moduleName m)) $ do
  for_ (moduleImports m) (modify . Namespace.union <=< importModule)

  decls <- for (moduleDecls m) $ \ decl ->
    (Just <$> elabDecl decl) `catchError` ((Nothing <$) . logError)
  pure m { moduleDecls = catMaybes decls }

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
            , Member (State Namespace) sig
            )
         => Spanned (Decl Qualified (Surface.Surface (Name Meta) ::: Surface.Surface (Name Meta)))
         -> m (Spanned (Decl Qualified (Core Qualified ::: Type Qualified)))
elabDecl (Decl d name (tm ::: ty) :~ span) = namespace (show name) . runReader span . fmap (:~ span) $ do
  ty' <- runNamespace (declare (elab ty))
  modify (Namespace.insert name (Entry (Nothing ::: ty')))
  -- scope <- get

  -- let ty'' = whnf scope ty'
  -- (names, _) <- un (orTerm (\ n -> \case
  --   Core.Pi (Im :< _) b | False -> Just (Im :< Local n, whnf scope (instantiate (pure (Local n)) b))
  --   _                            -> Nothing)) ty''
  -- tm ::: _ <- runNamespace (define (Core.weaken ty') (elab (Surface.lams names tm)))
  tm ::: _ <- runNamespace (define (Core.weaken ty') (elab tm))
  modify (Namespace.insert name (Entry (Just tm ::: ty')))
  pure (Decl d name (tm ::: ty'))

declare :: ( Carrier sig m
           , Effect sig
           , Member (Error Doc) sig
           , Member Naming sig
           , Member (Reader Namespace) sig
           , Member (Reader Span) sig
           )
        => ElabC (StateC Signature m) (Core (Name Meta) ::: Type (Name Meta))
        -> m (Core Qualified)
declare ty = evalState (mempty :: Signature) $ do
  (constraints, ty') <- runElab (goalIs Core.Type ty)
  subst <- solver constraints
  pure (Core.generalizeType (apply subst ty'))

define :: ( Carrier sig m
          , Effect sig
          , Member (Error Doc) sig
          , Member Naming sig
          , Member (Reader Namespace) sig
          , Member (Reader Span) sig
          )
       => Core (Name Meta)
       -> ElabC (StateC Signature m) (Core (Name Meta) ::: Type (Name Meta))
       -> m (Core Qualified ::: Type Qualified)
define ty tm = evalState (mempty :: Signature) $ do
  (constraints, tm') <- runElab (goalIs ty tm)
  subst <- solver constraints
  let ty' = Core.generalizeType (apply subst ty)
  (::: ty') <$> Core.strengthen (apply subst tm')

runNamespace :: (Carrier sig m, Member (State Namespace) sig) => ReaderC Namespace m a -> m a
runNamespace m = get >>= flip runReader m
