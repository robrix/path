{-# LANGUAGE MultiParamTypeClasses #-}
module Control.Monad.Module where

class (Functor f, Monad m) => RModule f m where
  (>>==) :: f a -> (a -> m b) -> f b

(>==>) :: RModule f m => (a -> f b) -> (b -> m c) -> a -> f c
f >==> g = \x -> f x >>== g
