{-# LANGUAGE DeriveFunctor, ExistentialQuantification, StandaloneDeriving #-}
module Control.Effect.Stack where

data Stack e m k
  = forall a . Push e (m a) (e -> a -> k)
  | Modify (e -> e) k

deriving instance Functor (Stack e m)
