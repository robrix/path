{-# LANGUAGE DeriveTraversable #-}
module Path.Problem where

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


data Equation a
  = a :===: a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infix 3 :===:


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
