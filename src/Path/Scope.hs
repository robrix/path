{-# LANGUAGE DataKinds, DeriveGeneric, DeriveTraversable, EmptyCase, FlexibleInstances, GADTs, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, StandaloneDeriving #-}
module Path.Scope where

import Control.Applicative (liftA2)
import Control.Effect.Carrier
import Control.Monad ((>=>), guard)
import Control.Monad.Module
import Control.Monad.Trans (MonadTrans (..))
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Function (on)
import Data.List (elemIndex)
import GHC.Generics (Generic1)
import Path.Pretty

data Var a b = B a | F b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance (Pretty b, Pretty f) => Pretty (Var b f) where
  pretty = \case
    B b -> pretty b
    F f -> pretty f

instance Bifoldable Var where
  bifoldMap f g = \case
    B a -> f a
    F a -> g a

instance Bitraversable Var where
  bitraverse f g = \case
    B a -> B <$> f a
    F a -> F <$> g a

instance Bifunctor Var where
  bimap f g = \case
    B a -> B (f a)
    F a -> F (g a)

instance Applicative (Var a) where
  pure = F
  B e <*> _ = B e
  F f <*> a = f <$> a

instance Monad (Var a) where
  B e >>= _ = B e
  F a >>= f = f a

var :: (a -> c) -> (b -> c) -> Var a b -> c
var z s = \case { B a -> z a ; F b -> s b }

match :: Applicative f => (b -> Either a c) -> b -> Var a (f c)
match f x = either B (F . pure) (f x)

matchM :: (Applicative f, Functor m) => (b -> m (Either a c)) -> b -> m (Var a (f c))
matchM f x = either B (F . pure) <$> f x

matchMaybe :: (b -> Maybe a) -> (b -> Either a b)
matchMaybe f a = maybe (Right a) Left (f a)


data Nat = Z | S Nat
  deriving (Eq, Ord, Show)

data Fin n where
  FZ :: Fin ('S n)
  FS :: Fin n -> Fin ('S n)

deriving instance Eq   (Fin n)
deriving instance Ord  (Fin n)
deriving instance Show (Fin n)

instance Pretty (Fin n) where
  pretty = prettyVar . finToInt

absurdFin :: Fin 'Z -> a
absurdFin v = case v of {}

finToInt :: Fin n -> Int
finToInt FZ     = 0
finToInt (FS n) = 1 + finToInt n

strengthenFin :: Fin ('S n) -> Maybe (Fin n)
strengthenFin FZ     = Nothing
strengthenFin (FS n) = Just n


data Vec n a where
  VZ :: Vec 'Z a
  VS :: a -> Vec n a -> Vec ('S n) a

deriving instance Eq   a => Eq   (Vec n a)
deriving instance Ord  a => Ord  (Vec n a)
deriving instance Show a => Show (Vec n a)

deriving instance Foldable    (Vec n)
deriving instance Functor     (Vec n)
deriving instance Traversable (Vec n)

(!) :: Vec n a -> Fin n -> a
VS h _ ! FZ   = h
VS _ t ! FS n = t ! n
VZ     ! n    = absurdFin n

infixl 9 !


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

handleScope
  :: (Traversable f, Monad m, Monad n)
  => f ()
  -> (forall x . f (m x) -> n (f x))
  -> Scope b m a
  -> Scope b n (f a)
handleScope state handler = toScope . fmap sequenceA . handler . (<$ state) . fromScope


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
instantiateEither f = unScope >=> var (f . Left) (>>= f . Right)

fromScope :: Monad f => Scope a f b -> f (Var a b)
fromScope = unScope >=> sequenceA

fromScopeFin :: Monad f => Scope () f (Var (Fin n) b) -> f (Var (Fin ('S n)) b)
fromScopeFin = unScope >=> var (const (pure (B FZ))) (fmap (first FS))

toScope :: Applicative f => f (Var a b) -> Scope a f b
toScope = Scope . fmap (fmap pure)

toScopeFin :: Applicative f => f (Var (Fin ('S n)) b) -> Scope () f (Var (Fin n) b)
toScopeFin = Scope . fmap (match (var (maybe (Left ()) (Right . B) . strengthenFin) (Right . F)))


-- | Like 'Scope', but allows the inner functor to vary. Useful for syntax like declaration scopes, case alternatives, etc., which can bind variables, but cannot (directly) consist solely of them.
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
instantiateTEither f = unScopeT >=>* var (f . Left) (>>= f . Right)

fromScopeT :: (RightModule t, Monad f) => ScopeT a t f b -> t f (Var a b)
fromScopeT = unScopeT >=>* sequenceA

toScopeT :: (Functor (t f), Applicative f) => t f (Var a b) -> ScopeT a t f b
toScopeT = ScopeT . fmap (fmap pure)
