{-# LANGUAGE DeriveTraversable, LambdaCase, RankNTypes, ScopedTypeVariables, TypeOperators #-}
module Path.Problem where

import Control.Monad (ap)
import Data.Foldable (foldl')
import Path.Name
import Path.Stack

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


data Equation a
  = a :===: a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infix 3 :===:


lam :: Eq a => a ::: Problem a -> Problem a -> Problem a
lam (n ::: t) b = Lam t (bind n b)

lams :: (Eq a, Foldable t) => t (a ::: Problem a) -> Problem a -> Problem a
lams names body = foldr lam body names

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
          Lam t (Scope b) -> lam (go t) (go (dist <$> b))
          f :$ a -> app f (go <$> a)
          Type -> ty
          Pi t (Scope b) -> pi (go t) (go (dist <$> b))

joinT :: Problem (Problem a) -> Problem a
joinT = gfoldT (\ t -> Ex t . Scope) U Type (\ t -> Lam t . Scope) (\ t -> Pi t . Scope) ($$*) (incr (pure Z) (fmap S))


-- | Bind occurrences of an 'Meta' in a 'Value' term, producing a 'Scope' in which the 'Meta' is bound.
bind :: Eq a => a -> Problem a -> Scope a
bind name = Scope . fmap (match name)

-- | Substitute a 'Problem' term for the free variable in a given 'Scope', producing a closed 'Problem' term.
instantiate :: Problem a -> Scope a -> Problem a
instantiate t (Scope b) = b >>= subst t . fmap pure
