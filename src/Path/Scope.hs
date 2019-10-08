{-# LANGUAGE DataKinds, DeriveGeneric, DeriveTraversable, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, StandaloneDeriving #-}
module Path.Scope where

import Control.Applicative (liftA2)
import Control.Effect.Carrier
import Control.Monad ((>=>), guard)
import Control.Monad.Trans (MonadTrans (..))
import Data.Bifunctor
import Data.Function (on)
import Data.List (elemIndex)
import GHC.Generics (Generic1)
import Path.Fin
import Path.Nat
import Syntax.Module
import Syntax.Var

var :: (a -> c) -> (b -> c) -> Var a b -> c
var z s = \case { B a -> z a ; F b -> s b }

match :: Applicative f => (b -> Var a c) -> b -> Var a (f c)
match f x = var B (F . pure) (f x)

matchM :: (Applicative f, Functor m) => (b -> m (Var a c)) -> b -> m (Var a (f c))
matchM f x = var B (F . pure) <$> f x

matchMaybe :: (b -> Maybe a) -> (b -> Var a b)
matchMaybe f a = maybe (F a) B (f a)


strengthen :: Functor f => f (Var (Fin 'Z) a) -> f a
strengthen = fmap (var absurdFin id)


newtype Scope a f b = Scope (f (Var a (f b)))
  deriving (Foldable, Functor, Generic1, Traversable)

unScope :: Scope a f b -> f (Var a (f b))
unScope (Scope s) = s

instance (Monad f, Eq  a, Eq  b, forall a . Eq  a => Eq  (f a)) => Eq  (Scope a f b) where
  (==) = (==) `on` fromScope

instance (Monad f, Ord a, Ord b, forall a . Eq  a => Eq  (f a)
                               , forall a . Ord a => Ord (f a)) => Ord (Scope a f b) where
  compare = compare `on` fromScope

deriving instance (Show a, Show b, forall a . Show a => Show (f a)) => Show (Scope a f b)

instance Applicative f => Applicative (Scope a f) where
  pure = Scope . pure . F . pure
  Scope f <*> Scope a = Scope (liftA2 (liftA2 (<*>)) f a)

instance Monad f => Monad (Scope a f) where
  Scope e >>= f = Scope (e >>= var (pure . B) (>>= unScope . f))

instance RightModule (Scope a) where
  Scope m >>=* f = Scope (fmap (>>= f) <$> m)

instance MonadTrans (Scope a) where
  lift = Scope . pure . F

instance HFunctor (Scope a) where
  hmap f = Scope . f . fmap (fmap f) . unScope


-- | Bind occurrences of a variable in a term, producing a term in which the variable is bound.
abstract1 :: (Applicative f, Eq a) => a -> f a -> Scope () f a
abstract1 n = abstract (guard . (== n))

abstract :: Applicative f => (b -> Maybe a) -> f b -> Scope a f b
abstract f = abstractVar (matchMaybe f)

abstractVar :: Applicative f => (b -> Var a c) -> f b -> Scope a f c
abstractVar f = Scope . fmap (match f) -- FIXME: succ as little of the expression as possible, cf https://twitter.com/ollfredo/status/1145776391826358273

abstractSimultaneous :: (Applicative f, Eq a) => [(a, f a)] -> [Scope Int f a]
abstractSimultaneous bs = map (abstract (`elemIndex` map fst bs) . snd) bs

-- | Substitute a term for the free variable in a given term, producing a closed term.
instantiate1 :: Monad f => f b -> Scope a f b -> f b
instantiate1 t = instantiate (const t)

instantiate :: Monad f => (a -> f b) -> Scope a f b -> f b
instantiate f = instantiateVar (var f pure)

instantiateVar :: Monad f => (Var a b -> f c) -> Scope a f b -> f c
instantiateVar f = unScope >=> var (f . B) (>>= f . F)

fromScope :: Monad f => Scope a f b -> f (Var a b)
fromScope = unScope >=> sequenceA

fromScopeFin :: Monad f => Scope () f (Var (Fin n) b) -> f (Var (Fin ('S n)) b)
fromScopeFin = unScope >=> var (const (pure (B FZ))) (fmap (first FS))

toScope :: Applicative f => f (Var a b) -> Scope a f b
toScope = Scope . fmap (fmap pure)

toScopeFin :: Applicative f => f (Var (Fin ('S n)) b) -> Scope () f (Var (Fin n) b)
toScopeFin = Scope . fmap (match (var (maybe (B ()) (F . B) . strengthenFin) (F . F)))


-- | Like 'Scope', but allows the inner functor to vary. Useful for syntax like declaration scopes, case alternatives, etc., which can abstract variables, but cannot (directly) consist solely of them.
newtype ScopeT a t f b = ScopeT (t f (Var a (f b)))
  deriving (Foldable, Functor, Generic1, Traversable)

unScopeT :: ScopeT a t f b -> t f (Var a (f b))
unScopeT (ScopeT s) = s

instance (RightModule t, Monad f, Eq  a, Eq  b, forall a . Eq  a => Eq  (t f a)) => Eq  (ScopeT a t f b) where
  (==) = (==) `on` fromScopeT

instance (RightModule t, Monad f, Ord a, Ord b, forall a . Eq  a => Eq  (t f a)
                                           , forall a . Ord a => Ord (t f a)) => Ord (ScopeT a t f b) where
  compare = compare `on` fromScopeT

deriving instance (Show a, Show b, forall a . Show a => Show (t f a)
                                 , forall a . Show a => Show (f a)) => Show (ScopeT a t f b)

instance (Applicative (t f), Applicative f) => Applicative (ScopeT a t f) where
  pure = ScopeT . pure . F . pure
  ScopeT f <*> ScopeT a = ScopeT (liftA2 (liftA2 (<*>)) f a)

instance (Monad (t f), MonadTrans t, Monad f) => Monad (ScopeT a t f) where
  ScopeT e >>= f = ScopeT (e >>= var (pure . B) ((>>= unScopeT . f) . lift))

instance (HFunctor t, forall g . Functor g => Functor (t g)) => RightModule (ScopeT b t) where
  ScopeT s >>=* k = ScopeT (fmap (>>= k) <$> s)

instance MonadTrans f => MonadTrans (ScopeT a f) where
  lift = ScopeT . lift . pure . F

instance (HFunctor t, forall g . Functor g => Functor (t g)) => HFunctor (ScopeT a t) where
  hmap f = ScopeT . hmap f . fmap (fmap f) . unScopeT


-- | Bind occurrences of a variable in a term, producing a term in which the variable is bound.
abstract1T :: (Functor (t f), Applicative f, Eq a) => a -> t f a -> ScopeT () t f a
abstract1T n = abstractT (guard . (== n))

abstractT :: (Functor (t f), Applicative f) => (b -> Maybe a) -> t f b -> ScopeT a t f b
abstractT f = abstractVarT (matchMaybe f)

abstractVarT :: (Functor (t f), Applicative f) => (b -> Var a c) -> t f b -> ScopeT a t f c
abstractVarT f = ScopeT . fmap (match f) -- FIXME: succ as little of the expression as possible, cf https://twitter.com/ollfredo/status/1145776391826358273

-- | Substitute a term for the free variable in a given term, producing a closed term.
instantiate1T :: (RightModule t, Monad f) => f b -> ScopeT a t f b -> t f b
instantiate1T t = instantiateT (const t)

instantiateT :: (RightModule t, Monad f) => (a -> f b) -> ScopeT a t f b -> t f b
instantiateT f = instantiateVarT (var f pure)

instantiateVarT :: (RightModule t, Monad f) => (Var a b -> f c) -> ScopeT a t f b -> t f c
instantiateVarT f = unScopeT >=>* var (f . B) (>>= f . F)

fromScopeT :: (RightModule t, Monad f) => ScopeT a t f b -> t f (Var a b)
fromScopeT = unScopeT >=>* sequenceA

toScopeT :: (Functor (t f), Applicative f) => t f (Var a b) -> ScopeT a t f b
toScopeT = ScopeT . fmap (fmap pure)
