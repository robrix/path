{-# LANGUAGE DeriveTraversable, FlexibleContexts, LambdaCase, RankNTypes, ScopedTypeVariables, TypeOperators #-}
module Path.Problem where

import Control.Applicative (Alternative(..))
import Control.Effect
import Control.Effect.Fail
import Control.Effect.Reader hiding (Local)
import Control.Monad (ap)
import Data.Foldable (foldl')
import qualified Data.Map as Map
import Path.Constraint (Equation(..))
import Path.Name
import qualified Path.Scope as Scope
import Path.Stack as Stack
import Prelude hiding (fail, pi)

data Problem a
  = Ex (Problem a) (Scope a)
  | U (Equation (Problem a))
  | Type
  | Lam (Problem a) (Scope a)
  | Pi (Problem a) (Scope a)
  | a :$ Stack (Problem a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype Scope a = Scope (Problem (Incr a))
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Problem where
  pure = (:$ Nil)
  (<*>) = ap

instance Monad Problem where
  a >>= f = joinT (f <$> a)


exists :: Eq a => a ::: Problem a -> Problem a -> Problem a
exists (n ::: t) b = Ex t (bind n b)

unexists :: Alternative m => a -> Problem a -> m (a ::: Problem a, Problem a)
unexists n (Ex t b) = pure (n ::: t, instantiate (pure n) b)
unexists _ _        = empty

(===) :: Problem a -> Problem a -> Problem a
p === q = U (p :===: q)

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

($$) :: Problem a -> Problem a -> Problem a
Lam _ b $$ v = instantiate v b
Pi  _ b $$ v = instantiate v b
n :$ vs $$ v = n :$ (vs :> v)
_       $$ _ = error "illegal application of Type"

($$*) :: Foldable t => Problem a -> t (Problem a) -> Problem a
v $$* sp = foldl' ($$) v sp


gfoldT :: forall m n b
       .  (forall a . n a -> n (Incr a) -> n a)
       -> (forall a . Equation (n a) -> n a)
       -> (forall a . n a)
       -> (forall a . n a -> n (Incr a) -> n a)
       -> (forall a . n a -> n (Incr a) -> n a)
       -> (forall a . m a -> Stack (n a) -> n a)
       -> (forall a . Incr (m a) -> m (Incr a))
       -> Problem (m b)
       -> n b
gfoldT ex u ty lam pi app dist = go
  where go :: Problem (m x) -> n x
        go = \case
          Ex t (Scope b) -> ex (go t) (go (dist <$> b))
          U (a :===: b) -> u (go a :===: go b)
          Type -> ty
          Lam t (Scope b) -> lam (go t) (go (dist <$> b))
          Pi t (Scope b) -> pi (go t) (go (dist <$> b))
          f :$ a -> app f (go <$> a)

joinT :: Problem (Problem a) -> Problem a
joinT = gfoldT (\ t -> Ex t . Scope) U Type (\ t -> Lam t . Scope) (\ t -> Pi t . Scope) ($$*) (incr (pure Z) (fmap S))


-- | Bind occurrences of an 'Meta' in a 'Value' term, producing a 'Scope' in which the 'Meta' is bound.
bind :: Eq a => a -> Problem a -> Scope a
bind name = Scope . fmap (match name)

-- | Substitute a 'Problem' term for the free variable in a given 'Scope', producing a closed 'Problem' term.
instantiate :: Problem a -> Scope a -> Problem a
instantiate t (Scope b) = b >>= subst t . fmap pure


assume :: ( Carrier sig m
          , Member (Reader (Stack (Gensym ::: Problem Meta))) sig
          , Member (Reader (Map.Map Qualified (Scope.Entry (Problem Meta)))) sig
          , MonadFail m
          )
       => Name
       -> m (Problem Meta ::: Problem Meta)
assume v = do
  _A <- have v
  pure (pure (Name v) ::: _A)

intro :: ( Carrier sig m
         , Member Naming sig
         , Member (Reader (Stack (Gensym ::: Problem Meta))) sig
         )
      => (Name -> m (Problem Meta ::: Problem Meta))
      -> m (Problem Meta ::: Problem Meta)
intro body = do
  _A <- meta Type
  x <- gensym "intro"
  _B <- x ::: _A |- meta Type
  u <- x ::: _A |- goalIs _B (body (Local x))
  pure (lam (qlocal x ::: _A) u ::: pi (qlocal x ::: _A) _B)

(-->) :: ( Carrier sig m
         , Member (Reader (Stack (Gensym ::: Problem Meta))) sig
         , Member Naming sig
         )
      => m (Problem Meta ::: Problem Meta)
      -> (Name -> m (Problem Meta ::: Problem Meta))
      -> m (Problem Meta ::: Problem Meta)
t --> body = do
  t' <- goalIs Type t
  x <- gensym "pi"
  b' <- x ::: t' |- goalIs Type (body (Local x))
  pure (pi (qlocal x ::: t') b' ::: Type)


goalIs :: ( Carrier sig m
          , Member Naming sig
          )
       => Problem Meta
       -> m (Problem Meta ::: Problem Meta)
       -> m (Problem Meta)
goalIs ty2 m = do
  tm1 ::: ty1 <- m
  tm2 <- meta (ty1 === ty2)
  pure (tm1 === tm2)

meta :: (Carrier sig m, Member Naming sig) => Problem Meta -> m (Problem Meta)
meta ty = do
  n <- gensym "meta"
  pure (exists (Meta n ::: ty) (pure (Meta n)))

(|-) :: (Carrier sig m, Member (Reader (Stack (Gensym ::: Problem Meta))) sig) => Gensym ::: Problem Meta -> m a -> m a
(|-) = local . flip (:>)

infix 5 |-

have :: ( Carrier sig m
        , Member (Reader (Stack (Gensym ::: Problem Meta))) sig
        , Member (Reader (Map.Map Qualified (Scope.Entry (Problem Meta)))) sig
        , MonadFail m
        )
     => Name
     -> m (Problem Meta)
have n = lookup n >>= maybe (fail ("free variable: " <> show n)) pure
  where lookup (Global n) = asks (fmap Scope.entryType . Map.lookup n)
        lookup (Local  n) = asks (fmap typedType . Stack.find ((== n) . typedTerm))
