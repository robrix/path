{-# LANGUAGE DeriveTraversable, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, StandaloneDeriving #-}
module Path.Scope where

import Control.Applicative (liftA2)
import Control.Monad ((>=>))
import Control.Monad.Module
import Control.Monad.Trans (MonadTrans (..))
import Data.Function (on)
import Data.List (elemIndex)

data Incr a b = Z a | S b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative (Incr a) where
  pure = S
  Z e <*> _ = Z e
  S f <*> a = f <$> a

instance Monad (Incr a) where
  Z e >>= _ = Z e
  S a >>= f = f a

match :: Applicative f => (b -> Either a c) -> b -> Incr a (f c)
match f x = either Z (S . pure) (f x)

toEither :: (b -> Maybe a) -> (b -> Either a b)
toEither f a = maybe (Right a) Left (f a)

fromIncr :: (a -> b) -> Incr a b -> b
fromIncr a = incr a id

incr :: (a -> c) -> (b -> c) -> Incr a b -> c
incr z s = \case { Z a -> z a ; S b -> s b }


newtype Scope a f b = Scope (f (Incr a (f b)))
  deriving (Foldable, Functor, Traversable)

unScope :: Scope a f b -> f (Incr a (f b))
unScope (Scope s) = s

instance (Monad f, Eq  a, Eq  b, forall a . Eq  a => Eq  (f a)) => Eq  (Scope a f b) where
  (==) = (==) `on` fromScope

instance (Monad f, Ord a, Ord b, forall a . Eq  a => Eq  (f a)
                               , forall a . Ord a => Ord (f a)) => Ord (Scope a f b) where
  compare = compare `on` fromScope

deriving instance (Show a, Show b, forall a . Show a => Show (f a)) => Show (Scope a f b)

instance Applicative f => Applicative (Scope a f) where
  pure = Scope . pure . S . pure
  Scope f <*> Scope a = Scope (liftA2 (liftA2 (<*>)) f a)

instance Monad f => Monad (Scope a f) where
  Scope e >>= f = Scope (e >>= incr (pure . Z) (>>= unScope . f))

instance Monad f => RModule (Scope a f) f where
  Scope m >>== f = Scope (fmap (>>= f) <$> m)

instance MonadTrans (Scope a) where
  lift = Scope . pure . S


-- | Bind occurrences of a variable in a term, producing a term in which the variable is bound.
bind :: Applicative f => (b -> Maybe a) -> f b -> Scope a f b
bind f = bindEither (toEither f)

bindEither :: Applicative f => (b -> Either a c) -> f b -> Scope a f c
bindEither f = Scope . fmap (match f) -- FIXME: succ as little of the expression as possible, cf https://twitter.com/ollfredo/status/1145776391826358273

bindSimultaneous :: (Applicative f, Eq a) => [(a, f a)] -> [Scope Int f a]
bindSimultaneous bs = map (bind (`elemIndex` map fst bs) . snd) bs

-- | Substitute a term for the free variable in a given term, producing a closed term.
instantiate :: Monad f => (a -> f b) -> Scope a f b -> f b
instantiate f = instantiateEither (either f pure)

instantiateEither :: Monad f => (Either a b -> f c) -> Scope a f b -> f c
instantiateEither f = unScope >=> incr (f . Left) (>>= f . Right)

fromScope :: Monad f => Scope a f b -> f (Incr a b)
fromScope = unScope >=> sequenceA

toScope :: Applicative f => f (Incr a b) -> Scope a f b
toScope = Scope . fmap (fmap pure)

foldScope :: (forall a . Incr z (n a) -> m (Incr z (n a)))
          -> (forall x y . (x -> m y) -> f x -> n y)
          -> (a -> m b)
          -> Scope z f a
          -> Scope z n b
foldScope k go h = Scope . go (k . fmap (go h)) . unScope


-- | Like 'Scope', but allows the inner functor to vary. Useful for syntax like declaration scopes, case alternatives, etc., which can bind variables, but cannot (directly) consist solely of them.
newtype ScopeH a f g b = ScopeH (f (Incr a (g b)))
  deriving (Foldable, Functor, Traversable)

unScopeH :: ScopeH a f g b -> f (Incr a (g b))
unScopeH (ScopeH s) = s

instance (RModule f g, Eq  a, Eq  b, forall a . Eq  a => Eq  (f a)) => Eq  (ScopeH a f g b) where
  (==) = (==) `on` fromScopeH

instance (RModule f g, Ord a, Ord b, forall a . Eq  a => Eq  (f a)
                                   , forall a . Ord a => Ord (f a)) => Ord (ScopeH a f g b) where
  compare = compare `on` fromScopeH

deriving instance (Show a, Show b, forall a . Show a => Show (f a)
                                 , forall a . Show a => Show (g a)) => Show (ScopeH a f g b)

instance (Applicative f, Applicative g) => Applicative (ScopeH a f g) where
  pure = ScopeH . pure . S . pure
  ScopeH f <*> ScopeH a = ScopeH (liftA2 (liftA2 (<*>)) f a)

instance (Functor f, Monad m) => RModule (ScopeH b f m) m where
  ScopeH s >>== k = ScopeH (fmap (>>= k) <$> s)

instance Applicative f => MonadTrans (ScopeH a f) where
  lift = ScopeH . pure . S


-- | Bind occurrences of a variable in a term, producing a term in which the variable is bound.
bindH :: (Functor f, Applicative g) => (b -> Maybe a) -> f b -> ScopeH a f g b
bindH f = ScopeH . fmap (match (toEither f)) -- FIXME: succ as little of the expression as possible, cf https://twitter.com/ollfredo/status/1145776391826358273

-- | Substitute a term for the free variable in a given term, producing a closed term.
instantiateH :: RModule f g => (a -> g b) -> ScopeH a f g b -> f b
instantiateH f = unScopeH >==> fromIncr f

fromScopeH :: RModule f g => ScopeH a f g b -> f (Incr a b)
fromScopeH = unScopeH >==> sequenceA

toScopeH :: (Functor f, Applicative g) => f (Incr a b) -> ScopeH a f g b
toScopeH = ScopeH . fmap (fmap pure)
