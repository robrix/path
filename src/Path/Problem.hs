{-# LANGUAGE DeriveTraversable, FlexibleContexts, LambdaCase, RankNTypes, ScopedTypeVariables, TypeOperators #-}
module Path.Problem where

import Control.Applicative (Alternative(..))
import Control.Effect
import Control.Effect.Fail
import Control.Effect.Reader hiding (Local)
import Control.Effect.State
import Control.Monad (ap)
import Path.Constraint (Equation(..))
import qualified Path.Core as Core
import Path.Module
import Path.Name
import Path.Plicity (Plicit(..))
import Path.Stack as Stack
import Prelude hiding (fail, pi)
import Text.Trifecta.Rendering (Span(..), Spanned(..))

data Problem a
  = Ex (Problem a) (Scope a)
  | U (Equation (Problem a))
  | Var (Name a)
  | Type
  | Lam (Problem a) (Scope a)
  | Pi (Problem a) (Scope a)
  | Problem a :$ Problem a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype Scope a = Scope (Problem (Incr a))
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Problem where
  pure = Var . Local
  (<*>) = ap

instance Monad Problem where
  a >>= f = joinT (f <$> a)


exists :: Eq a => a ::: Problem a -> Problem a -> Problem a
exists (n ::: t) b = Ex t (bind n b)

unexists :: Alternative m => a -> Problem a -> m (a ::: Problem a, Problem a)
unexists n (Ex t b) = pure (n ::: t, instantiate (pure n) b)
unexists _ _        = empty

(===) :: Eq a => Problem a -> Problem a -> Problem a
p === q
  | p == q    = p
  | otherwise = U (p :===: q)

infixr 3 ===

lam :: Eq a => a ::: Problem a -> Problem a -> Problem a
lam (n ::: t) b = Lam t (bind n b)

lams :: (Eq a, Foldable t) => t (a ::: Problem a) -> Problem a -> Problem a
lams names body = foldr lam body names

unlam :: Alternative m => a -> Problem a -> m (a ::: Problem a, Problem a)
unlam n (Lam t b) = pure (n ::: t, instantiate (pure n) b)
unlam _ _         = empty

pi :: Eq a => a ::: Problem a -> Problem a -> Problem a
pi (n ::: t) b = Pi t (bind n b)

-- | Wrap a type in a sequence of pi bindings.
pis :: (Eq a, Foldable t) => t (a ::: Problem a) -> Problem a -> Problem a
pis names body = foldr pi body names

unpi :: Alternative m => a -> Problem a -> m (a ::: Problem a, Problem a)
unpi n (Pi t b) = pure (n ::: t, instantiate (pure n) b)
unpi _ _        = empty


gfoldT :: forall m n b
       .  (forall a . n a -> n (Incr a) -> n a)
       -> (forall a . Equation (n a) -> n a)
       -> (forall a . Name (m a) -> n a)
       -> (forall a . n a)
       -> (forall a . n a -> n (Incr a) -> n a)
       -> (forall a . n a -> n (Incr a) -> n a)
       -> (forall a . n a -> n a -> n a)
       -> (forall a . Incr (m a) -> m (Incr a))
       -> Problem (m b)
       -> n b
gfoldT ex u var ty lam pi app dist = go
  where go :: Problem (m x) -> n x
        go = \case
          Ex t (Scope b) -> ex (go t) (go (dist <$> b))
          U (a :===: b) -> u (go a :===: go b)
          Var a -> var a
          Type -> ty
          Lam t (Scope b) -> lam (go t) (go (dist <$> b))
          Pi t (Scope b) -> pi (go t) (go (dist <$> b))
          f :$ a -> go f `app` go a

joinT :: Problem (Problem a) -> Problem a
joinT = gfoldT (\ t -> Ex t . Scope) U (name id (Var . Global)) Type (\ t -> Lam t . Scope) (\ t -> Pi t . Scope) (:$) (incr (pure Z) (fmap S))


-- | Bind occurrences of a name in a 'Value' term, producing a 'Scope' in which the name is bound.
bind :: Eq a => a -> Problem a -> Scope a
bind name = Scope . fmap (match name)

-- | Substitute a 'Problem' term for the free variable in a given 'Scope', producing a closed 'Problem' term.
instantiate :: Problem a -> Scope a -> Problem a
instantiate t (Scope b) = b >>= subst t . fmap pure


type Context = Stack (Binding ::: Problem Gensym)

assume :: ( Carrier sig m
          , Member (Reader Context) sig
          , MonadFail m
          )
       => Name Gensym
       -> m (Problem Gensym ::: Problem Gensym)
assume v = do
  _A <- have v
  pure (Var v ::: _A)

intro :: ( Carrier sig m
         , Member Naming sig
         , Member (Reader Context) sig
         )
      => (Gensym -> m (Problem Gensym ::: Problem Gensym))
      -> m (Problem Gensym ::: Problem Gensym)
intro body = do
  _A <- meta Type
  x <- gensym "intro"
  _B <- ForAll x ::: _A |- meta Type
  u <- ForAll x ::: _A |- goalIs _B (body x)
  pure (lam (x ::: _A) u ::: pi (x ::: _A) _B)

(-->) :: ( Carrier sig m
         , Member Naming sig
         , Member (Reader Context) sig
         )
      => m (Problem Gensym ::: Problem Gensym)
      -> (Gensym -> m (Problem Gensym ::: Problem Gensym))
      -> m (Problem Gensym ::: Problem Gensym)
t --> body = do
  t' <- goalIs Type t
  x <- gensym "pi"
  b' <- ForAll x ::: t' |- goalIs Type (body x)
  pure (pi (x ::: t') b' ::: Type)

app :: ( Carrier sig m
       , Member Naming sig
       , Member (Reader Context) sig
       )
    => m (Problem Gensym ::: Problem Gensym)
    -> m (Problem Gensym ::: Problem Gensym)
    -> m (Problem Gensym ::: Problem Gensym)
app f a = do
  _A <- meta Type
  x <- gensym "app"
  _B <- ForAll x ::: _A |- meta Type
  let _F = pi (x ::: _A) _B
  f' <- goalIs _F f
  a' <- goalIs _A a
  pure (f' :$ a' ::: _F :$ a')


goalIs :: ( Carrier sig m
          , Member Naming sig
          )
       => Problem Gensym
       -> m (Problem Gensym ::: Problem Gensym)
       -> m (Problem Gensym)
goalIs ty2 m = do
  tm1 ::: ty1 <- m
  tm2 <- meta (ty1 === ty2)
  pure (tm1 === tm2)

meta :: (Carrier sig m, Member Naming sig) => Problem Gensym -> m (Problem Gensym)
meta ty = do
  n <- gensym "meta"
  pure (exists (n ::: ty) (pure n))

(|-) :: (Carrier sig m, Member (Reader Context) sig) => Binding ::: Problem Gensym -> m a -> m a
(|-) = local . flip (:>)

infix 3 |-

have :: ( Carrier sig m
        , Member (Reader Context) sig
        , MonadFail m
        )
     => Name Gensym
     -> m (Problem Gensym)
have n = lookup n >>= maybe (fail ("free variable: " <> show n)) pure
  where lookup n = asks (fmap typedType . Stack.find ((== n) . bindingName . typedTerm))


spanIs :: (Carrier sig m, Member (Reader Span) sig) => Span -> m a -> m a
spanIs span = local (const span)

elab :: ( Carrier sig m
        , Member Naming sig
        , Member (Reader Context) sig
        , Member (Reader Span) sig
        , MonadFail m
        )
     => Core.Core Gensym
     -> m (Problem Gensym ::: Problem Gensym)
elab = \case
  Core.Var n -> assume n
  Core.Lam _ b -> intro (\ n' -> elab (Core.instantiate (pure n') b))
  f Core.:$ (_ :< a) -> app (elab f) (elab a)
  Core.Type -> pure (Type ::: Type)
  Core.Pi (_ :< (_, _, t)) b -> elab t --> \ n' -> elab (Core.instantiate (pure n') b)
  Core.Hole h -> (pure h :::) <$> meta Type
  Core.Ann ann b -> spanIs ann (elab b)

elabDecl :: ( Carrier sig m
            , Member Naming sig
            , Member (State Context) sig
            , MonadFail m
            )
         => Spanned (Decl Qualified (Core.Core Gensym ::: Core.Core Gensym))
         -> m (Spanned (Decl Qualified (Problem Gensym ::: Problem Gensym)))
elabDecl (Decl d name (tm ::: ty) :~ span) = namespace (show name) . runReader span . fmap (:~ span) $ do
  ctx <- get
  ty' <- runReader ctx (declare    (elab ty))
  def <- meta ty'
  tm' <- runReader (ctx :> Define (Global name := def) ::: ty') (define ty' (elab tm))
  put (ctx :> Define (Global name := tm') ::: ty')
  pure (Decl d name (tm' ::: ty'))

declare :: ( Carrier sig m
           , Member Naming sig
           , Member (Reader Context) sig
           , MonadFail m
           )
        => m (Problem Gensym ::: Problem Gensym)
        -> m (Problem Gensym)
declare ty = goalIs Type ty >>= simplify

define :: ( Carrier sig m
          , Member Naming sig
          , Member (Reader Context) sig
          , MonadFail m
          )
       => Problem Gensym
       -> m (Problem Gensym ::: Problem Gensym)
       -> m (Problem Gensym)
define ty tm = goalIs ty tm >>= simplify


simplify :: ( Carrier sig m
            , Member Naming sig
            , Member (Reader Context) sig
            , MonadFail m
            )
         => Problem Gensym
         -> m (Problem Gensym)
simplify = \case
  Ex t b -> do
    n <- gensym "ex"
    t' <- simplify t
    b' <- Exists n ::: t' |- simplify (instantiate (pure n) b)
    pure (exists (n ::: t') b')
  U (t1 :===: t2)
    | t1 == t2  -> pure t1
  U (Ex t1 b1 :===: Ex t2 b2) -> do
    n <- gensym "ex"
    t' <- simplify (t1 === t2)
    b' <- Exists n ::: t' |- simplify (instantiate (pure n) b1 === instantiate (pure n) b2)
    pure (exists (n ::: t') b')
  U (Ex t1 b1 :===: tm2) -> do
    n <- gensym "ex"
    t1' <- simplify t1
    Exists n ::: t1' |- exists (n ::: t1') <$> simplify (instantiate (pure n) b1 === tm2)
  U (tm1 :===: Ex t2 b2) -> do
    n <- gensym "ex"
    t2' <- simplify t2
    Exists n ::: t2' |- exists (n ::: t2') <$> simplify (tm1 === instantiate (pure n) b2)
  U (Pi t1 b1 :===: Pi t2 b2) -> do
    n <- gensym "pi"
    t' <- simplify (t1 === t2)
    ForAll n ::: t' |- pi (n ::: t') <$> simplify (instantiate (pure n) b1 === instantiate (pure n) b2)
  U (Lam t1 b1 :===: Lam t2 b2) -> do
    n <- gensym "lam"
    t' <- simplify (t1 === t2)
    ForAll n ::: t' |- lam (n ::: t') <$> simplify (instantiate (pure n) b1 === instantiate (pure n) b2)
  U other -> fail $ "no rule to simplify: " <> show other
  Var a -> pure (Var a)
  Type -> pure Type
  Lam t b -> do
    n <- gensym "lam"
    t' <- simplify t
    b' <- ForAll n ::: t' |- simplify (instantiate (pure n) b)
    pure (lam (n ::: t') b')
  Pi t b -> do
    n <- gensym "pi"
    t' <- simplify t
    b' <- ForAll n ::: t' |- simplify (instantiate (pure n) b)
    pure (pi (n ::: t') b')
  f :$ a -> do
    f' <- simplify f
    a' <- simplify a
    pure (f' :$ a')

data a := b = a := b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infix 1 :=

data Binding
  = Define (Name Gensym := Problem Gensym)
  | Exists Gensym
  | ForAll Gensym
  deriving (Eq, Ord, Show)

bindingName :: Binding -> Name Gensym
bindingName (Define (n := _)) = n
bindingName (Exists  n)       = Local n
bindingName (ForAll  n)       = Local n
