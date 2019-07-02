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


newtype Scope f a = Scope (f (Incr () (f a)))
  deriving (Foldable, Functor, Traversable)

unScope :: Scope f a -> f (Incr () (f a))
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
  Scope e >>= f = Scope (e >>= incr (pure . Z) (>>= unScope . f))

instance MonadTrans Scope where
  lift = Scope . pure . S


-- | Bind occurrences of a variable in a term, producing a term in which the variable is bound.
bind :: (Applicative f, Eq a) => a -> f a -> Scope f a
bind name = Scope . fmap (match eq) -- FIXME: succ as little of the expression as possible, cf https://twitter.com/ollfredo/status/1145776391826358273
  where eq x | name == x = Just ()
             | otherwise = Nothing

-- | Substitute a term for the free variable in a given term, producing a closed term.
instantiate :: Monad f => f a -> Scope f a -> f a
instantiate t = unScope >=> fromIncr (const t)

flattenScope :: Monad f => Scope f a -> f (Incr () a)
flattenScope = unScope >=> sequenceA

foldScope :: (forall a . Incr () (n a) -> m (Incr () (n a)))
          -> (forall x y . (x -> m y) -> f x -> n y)
          -> (a -> m b)
          -> Scope f a
          -> Scope n b
foldScope k go h = Scope . go (k . fmap (go h)) . unScope
