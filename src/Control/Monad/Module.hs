{-# LANGUAGE FlexibleInstances, QuantifiedConstraints, MultiParamTypeClasses, TypeOperators #-}
module Control.Monad.Module where

import Control.Effect.Carrier

class (forall g . Functor g => Functor (f g), HFunctor f) => HRModule f where
  (>>=*) :: Monad m => f m a -> (a -> m b) -> f m b
  infixl 1 >>=*

instance (HRModule f, HRModule g) => HRModule (f :+: g) where
  L l >>=* f = L (l >>=* f)
  R r >>=* f = R (r >>=* f)


(>=>*) :: (HRModule f, Monad m) => (a -> f m b) -> (b -> m c) -> (a -> f m c)
f >=>* g = \x -> f x >>=* g

infixl 1 >=>*

(<=<*) :: (HRModule f, Monad m) => (b -> m c) -> (a -> f m b) -> (a -> f m c)
g <=<* f = \x -> f x >>=* g

infixl 1 <=<*

hjoinr :: (HRModule f, Monad m) => f m (m a) -> f m a
hjoinr = (>>=* id)


class (forall g . Functor g => Functor (f g), HFunctor f) => HLModule f where
  (*>>=) :: Monad m => m a -> (a -> f m b) -> f m b
  infixl 1 *>>=

(*>=>) :: (HLModule f, Monad m) => (a -> m b) -> (b -> f m c) -> (a -> f m c)
f *>=> g = \x -> f x *>>= g

infixl 1 *>=>

(*<=<) :: (HLModule f, Monad m) => (b -> f m c) -> (a -> m b) -> (a -> f m c)
g *<=< f = \x -> f x *>>= g

infixl 1 *<=<

hjoinl :: (HLModule f, Monad m) => m (f m a) -> f m a
hjoinl = (*>>= id)
