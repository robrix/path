{-# LANGUAGE DeriveTraversable, LambdaCase, QuantifiedConstraints, RankNTypes, StandaloneDeriving #-}
module Path.Scope where

import Control.Applicative (liftA2)
import Control.Monad ((>=>))
import Control.Monad.Trans (MonadTrans (..))
import Data.Function (on)

data Incr a = Z | S a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Incr where
  pure = S
  Z   <*> _ = Z
  S f <*> a = f <$> a

instance Monad Incr where
  Z   >>= _ = Z
  S a >>= f = f a

match :: (Applicative f, Eq a) => a -> a -> Incr (f a)
match x y | x == y    = Z
          | otherwise = S (pure y)

subst :: a -> Incr a -> a
subst a = incr a id

incr :: b -> (a -> b) -> Incr a -> b
incr z s = \case { Z -> z ; S a -> s a }


newtype Scope f a = Scope (f (Incr (f a)))
  deriving (Foldable, Functor, Traversable)

unScope :: Scope f a -> f (Incr (f a))
unScope (Scope s) = s

instance (Monad f, Eq  a, forall a . Eq  a => Eq  (f a)) => Eq  (Scope f a) where
  (==) = (==) `on` flattenScope

instance (Monad f, Ord a, forall a . Eq  a => Eq  (f a)
                        , forall a . Ord a => Ord (f a)) => Ord (Scope f a) where
  compare = compare `on` flattenScope

deriving instance (Show a, forall a . Show a => Show (f a)) => Show (Scope f a)

instance Applicative f => Applicative (Scope f) where
  pure = Scope . pure . S . pure
  Scope f <*> Scope a = Scope (liftA2 (liftA2 (<*>)) f a)

instance Monad f => Monad (Scope f) where
  Scope e >>= f = Scope (e >>= incr (pure Z) (>>= unScope . f))

instance MonadTrans Scope where
  lift = Scope . pure . S


-- | Bind occurrences of a variable in a term, producing a term in which the variable is bound.
bind :: (Applicative f, Eq a) => a -> f a -> Scope f a
bind name = Scope . fmap (match name) -- FIXME: succ as little of the expression as possible, cf https://twitter.com/ollfredo/status/1145776391826358273

-- | Substitute a term for the free variable in a given term, producing a closed term.
instantiate :: Monad f => f a -> Scope f a -> f a
instantiate t = unScope >=> subst t

flattenScope :: Monad f => Scope f a -> f (Incr a)
flattenScope = unScope >=> sequenceA

foldScope :: (forall a . Incr (n a) -> m (Incr (n a)))
          -> (forall x y . (x -> m y) -> f x -> n y)
          -> (a -> m b)
          -> Scope f a
          -> Scope n b
foldScope k go h = Scope . go (k . fmap (go h)) . unScope
