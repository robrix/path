{-# LANGUAGE DeriveTraversable, LambdaCase, QuantifiedConstraints, RankNTypes, StandaloneDeriving #-}
module Path.Scope where

import Control.Applicative (liftA2)
import Control.Monad ((>=>))
import Control.Monad.Trans (MonadTrans (..))
import Data.Function (on)

data Incr a b = Z a | S b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative (Incr a) where
  pure = S
  Z e <*> _ = Z e
  S f <*> a = f <$> a

instance Monad (Incr a) where
  Z e >>= _ = Z e
  S a >>= f = f a

match :: Applicative f => (b -> Maybe a) -> b -> Incr a (f b)
match f x | Just y <- f x = Z y
          | otherwise     = S (pure x)

fromIncr :: (a -> b) -> Incr a b -> b
fromIncr a = incr a id

incr :: (a -> c) -> (b -> c) -> Incr a b -> c
incr z s = \case { Z a -> z a ; S b -> s b }


newtype Scope a f b = Scope (f (Incr a (f b)))
  deriving (Foldable, Functor, Traversable)

unScope :: Scope a f b -> f (Incr a (f b))
unScope (Scope s) = s

instance (Monad f, Eq  a, Eq  b, forall a . Eq  a => Eq  (f a)) => Eq  (Scope a f b) where
  (==) = (==) `on` flattenScope

instance (Monad f, Ord a, Ord b, forall a . Eq  a => Eq  (f a)
                               , forall a . Ord a => Ord (f a)) => Ord (Scope a f b) where
  compare = compare `on` flattenScope

deriving instance (Show a, Show b, forall a . Show a => Show (f a)) => Show (Scope a f b)

instance Applicative f => Applicative (Scope a f) where
  pure = Scope . pure . S . pure
  Scope f <*> Scope a = Scope (liftA2 (liftA2 (<*>)) f a)

instance Monad f => Monad (Scope a f) where
  Scope e >>= f = Scope (e >>= incr (pure . Z) (>>= unScope . f))

instance MonadTrans (Scope a) where
  lift = Scope . pure . S


-- | Bind occurrences of a variable in a term, producing a term in which the variable is bound.
bind :: Applicative f => (b -> Maybe a) -> f b -> Scope a f b
bind f = Scope . fmap (match f) -- FIXME: succ as little of the expression as possible, cf https://twitter.com/ollfredo/status/1145776391826358273

-- | Substitute a term for the free variable in a given term, producing a closed term.
instantiate :: Monad f => (a -> f b) -> Scope a f b -> f b
instantiate f = unScope >=> fromIncr f

flattenScope :: Monad f => Scope a f b -> f (Incr a b)
flattenScope = unScope >=> sequenceA

foldScope :: (forall a . Incr z (n a) -> m (Incr z (n a)))
          -> (forall x y . (x -> m y) -> f x -> n y)
          -> (a -> m b)
          -> Scope z f a
          -> Scope z n b
foldScope k go h = Scope . go (k . fmap (go h)) . unScope
