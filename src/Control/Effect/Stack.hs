{-# LANGUAGE DeriveFunctor, ExistentialQuantification, StandaloneDeriving #-}
module Control.Effect.Stack where

import Control.Effect.Carrier

data Stack e m k
  = forall a . Push e (m a) (e -> a -> k)
  | Modify (e -> e) k

deriving instance Functor (Stack e m)

instance HFunctor (Stack e) where
  hmap f (Push e m k) = Push e (f m) k
  hmap _ (Modify f k) = Modify f     k
