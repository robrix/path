{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, TypeOperators #-}
module Control.Monad.Module where

import GHC.Generics

class (Functor f, Monad m) => RModule f m where
  (>>=*) :: f a -> (a -> m b) -> f b

(>=>*) :: RModule f m => (a -> f b) -> (b -> m c) -> (a -> f c)
f >=>* g = \x -> f x >>=* g

(<=<*) :: RModule f m => (b -> m c) -> (a -> f b) -> (a -> f c)
g <=<* f = \x -> f x >>=* g

joinr :: RModule f m => f (m a) -> f a
joinr = (>>=* id)


instance (Functor f, RModule g h) => RModule (f :.: g) h where
  Comp1 a >>=* f = Comp1 (fmap (>>=* f) a)


class (Functor f, Monad m) => LModule m f where
  (*>>=) :: m a -> (a -> f b) -> f b

(*>=>) :: LModule m f => (a -> m b) -> (b -> f c) -> (a -> f c)
f *>=> g = \x -> f x *>>= g

(*<=<) :: LModule m f => (b -> f c) -> (a -> m b) -> (a -> f c)
g *<=< f = \x -> f x *>>= g

joinl :: LModule m f => m (f a) -> f a
joinl = (*>>= id)
