{-# LANGUAGE ExistentialQuantification #-}
module Control.Effect.Stack where

data Stack e m k
  = forall a . Push e (m a) (e -> a -> k)
