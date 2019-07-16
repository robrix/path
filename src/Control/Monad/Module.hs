{-# LANGUAGE FlexibleInstances, QuantifiedConstraints, MultiParamTypeClasses, TypeOperators #-}
module Control.Monad.Module where

import Control.Effect.Carrier
import GHC.Generics ((:.:) (..))

class (Functor f, Monad m) => RModule f m where
  (>>=*) :: f a -> (a -> m b) -> f b
  infixl 1 >>=*

(>=>*) :: RModule f m => (a -> f b) -> (b -> m c) -> (a -> f c)
f >=>* g = \x -> f x >>=* g

infixl 1 >=>*

(<=<*) :: RModule f m => (b -> m c) -> (a -> f b) -> (a -> f c)
g <=<* f = \x -> f x >>=* g

infixl 1 <=<*

joinr :: RModule f m => f (m a) -> f a
joinr = (>>=* id)


instance (Functor f, RModule g h) => RModule (f :.: g) h where
  Comp1 a >>=* f = Comp1 (fmap (>>=* f) a)


class (Functor f, Monad m) => LModule m f where
  (*>>=) :: m a -> (a -> f b) -> f b
  infixl 1 *>>=

(*>=>) :: LModule m f => (a -> m b) -> (b -> f c) -> (a -> f c)
f *>=> g = \x -> f x *>>= g

infixl 1 *>=>

(*<=<) :: LModule m f => (b -> f c) -> (a -> m b) -> (a -> f c)
g *<=< f = \x -> f x *>>= g

infixl 1 *<=<

joinl :: LModule m f => m (f a) -> f a
joinl = (*>>= id)


class (forall g . Functor g => Functor (f g), HFunctor f) => HRModule f where
  (>>=**) :: Monad m => f m a -> (a -> m b) -> f m b
  infixl 1 >>=**

instance (HRModule f, HRModule g) => HRModule (f :+: g) where
  L l >>=** f = L (l >>=** f)
  R r >>=** f = R (r >>=** f)


(>=>**) :: (HRModule f, Monad m) => (a -> f m b) -> (b -> m c) -> (a -> f m c)
f >=>** g = \x -> f x >>=** g

infixl 1 >=>**

(<=<**) :: (HRModule f, Monad m) => (b -> m c) -> (a -> f m b) -> (a -> f m c)
g <=<** f = \x -> f x >>=** g

infixl 1 <=<**

hjoinr :: (HRModule f, Monad m) => f m (m a) -> f m a
hjoinr = (>>=** id)


class (forall g . Functor g => Functor (f g), HFunctor f) => HLModule f where
  (**>>=) :: Monad m => m a -> (a -> f m b) -> f m b
  infixl 1 **>>=

(**>=>) :: (HLModule f, Monad m) => (a -> m b) -> (b -> f m c) -> (a -> f m c)
f **>=> g = \x -> f x **>>= g

infixl 1 **>=>

(**<=<) :: (HLModule f, Monad m) => (b -> f m c) -> (a -> m b) -> (a -> f m c)
g **<=< f = \x -> f x **>>= g

infixl 1 **<=<

hjoinl :: (HLModule f, Monad m) => m (f m a) -> f m a
hjoinl = (**>>= id)
