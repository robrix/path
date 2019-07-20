{-# LANGUAGE DeriveGeneric, DeriveTraversable, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, StandaloneDeriving #-}
module Path.Scope where

import Control.Applicative (liftA2)
import Control.Effect.Carrier
import Control.Monad ((>=>), guard)
import Control.Monad.Module
import Control.Monad.Trans (MonadTrans (..))
import Data.Function (on)
import Data.List (elemIndex)
import GHC.Generics (Generic1)

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

matchM :: (Applicative f, Functor m) => (b -> m (Either a c)) -> b -> m (Incr a (f c))
matchM f x = either Z (S . pure) <$> f x

matchMaybe :: (b -> Maybe a) -> (b -> Either a b)
matchMaybe f a = maybe (Right a) Left (f a)

fromIncr :: (a -> b) -> Incr a b -> b
fromIncr a = incr a id

incr :: (a -> c) -> (b -> c) -> Incr a b -> c
incr z s = \case { Z a -> z a ; S b -> s b }


newtype Scope a f b = Scope (f (Incr a (f b)))
  deriving (Foldable, Functor, Generic1, Traversable)

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

instance RightModule (Scope a) where
  Scope m >>=* f = Scope (fmap (>>= f) <$> m)

instance MonadTrans (Scope a) where
  lift = Scope . pure . S

instance HFunctor (Scope a) where
  hmap f = Scope . f . fmap (fmap f) . unScope


-- | Bind occurrences of a variable in a term, producing a term in which the variable is bound.
bind1 :: (Applicative f, Eq a) => a -> f a -> Scope () f a
bind1 n = bind (guard . (== n))

bind :: Applicative f => (b -> Maybe a) -> f b -> Scope a f b
bind f = bindEither (matchMaybe f)

bindEither :: Applicative f => (b -> Either a c) -> f b -> Scope a f c
bindEither f = Scope . fmap (match f) -- FIXME: succ as little of the expression as possible, cf https://twitter.com/ollfredo/status/1145776391826358273

bindSimultaneous :: (Applicative f, Eq a) => [(a, f a)] -> [Scope Int f a]
bindSimultaneous bs = map (bind (`elemIndex` map fst bs) . snd) bs

-- | Substitute a term for the free variable in a given term, producing a closed term.
instantiate1 :: Monad f => f b -> Scope a f b -> f b
instantiate1 t = instantiate (const t)

instantiate :: Monad f => (a -> f b) -> Scope a f b -> f b
instantiate f = instantiateEither (either f pure)

instantiateEither :: Monad f => (Either a b -> f c) -> Scope a f b -> f c
instantiateEither f = unScope >=> incr (f . Left) (>>= f . Right)

fromScope :: Monad f => Scope a f b -> f (Incr a b)
fromScope = unScope >=> sequenceA

toScope :: Applicative f => f (Incr a b) -> Scope a f b
toScope = Scope . fmap (fmap pure)


-- | Like 'Scope', but allows the inner functor to vary. Useful for syntax like declaration scopes, case alternatives, etc., which can bind variables, but cannot (directly) consist solely of them.
newtype ScopeT a t f b = ScopeT (t f (Incr a (f b)))
  deriving (Foldable, Functor, Generic1, Traversable)

unScopeT :: ScopeT a t f b -> t f (Incr a (f b))
unScopeT (ScopeT s) = s

instance (RightModule t, Monad f, Eq  a, Eq  b, forall a . Eq  a => Eq  (t f a)) => Eq  (ScopeT a t f b) where
  (==) = (==) `on` fromScopeT

instance (RightModule t, Monad f, Ord a, Ord b, forall a . Eq  a => Eq  (t f a)
                                           , forall a . Ord a => Ord (t f a)) => Ord (ScopeT a t f b) where
  compare = compare `on` fromScopeT

deriving instance (Show a, Show b, forall a . Show a => Show (t f a)
                                 , forall a . Show a => Show (f a)) => Show (ScopeT a t f b)

instance (Applicative (t f), Applicative f) => Applicative (ScopeT a t f) where
  pure = ScopeT . pure . S . pure
  ScopeT f <*> ScopeT a = ScopeT (liftA2 (liftA2 (<*>)) f a)

instance (Monad (t f), MonadTrans t, Monad f) => Monad (ScopeT a t f) where
  ScopeT e >>= f = ScopeT (e >>= incr (pure . Z) ((>>= unScopeT . f) . lift))

instance (HFunctor t, forall g . Functor g => Functor (t g)) => RightModule (ScopeT b t) where
  ScopeT s >>=* k = ScopeT (fmap (>>= k) <$> s)

instance MonadTrans f => MonadTrans (ScopeT a f) where
  lift = ScopeT . lift . pure . S

instance (HFunctor t, forall g . Functor g => Functor (t g)) => HFunctor (ScopeT a t) where
  hmap f = ScopeT . hmap f . fmap (fmap f) . unScopeT


-- | Bind occurrences of a variable in a term, producing a term in which the variable is bound.
bind1T :: (Functor (t f), Applicative f, Eq a) => a -> t f a -> ScopeT () t f a
bind1T n = bindT (guard . (== n))

bindT :: (Functor (t f), Applicative f) => (b -> Maybe a) -> t f b -> ScopeT a t f b
bindT f = bindTEither (matchMaybe f)

bindTEither :: (Functor (t f), Applicative f) => (b -> Either a c) -> t f b -> ScopeT a t f c
bindTEither f = ScopeT . fmap (match f) -- FIXME: succ as little of the expression as possible, cf https://twitter.com/ollfredo/status/1145776391826358273

-- | Substitute a term for the free variable in a given term, producing a closed term.
instantiate1T :: (RightModule t, Monad f) => f b -> ScopeT a t f b -> t f b
instantiate1T t = instantiateT (const t)

instantiateT :: (RightModule t, Monad f) => (a -> f b) -> ScopeT a t f b -> t f b
instantiateT f = instantiateTEither (either f pure)

instantiateTEither :: (RightModule t, Monad f) => (Either a b -> f c) -> ScopeT a t f b -> t f c
instantiateTEither f = unScopeT >=>* incr (f . Left) (>>= f . Right)

fromScopeT :: (RightModule t, Monad f) => ScopeT a t f b -> t f (Incr a b)
fromScopeT = unScopeT >=>* sequenceA

toScopeT :: (Functor (t f), Applicative f) => t f (Incr a b) -> ScopeT a t f b
toScopeT = ScopeT . fmap (fmap pure)
