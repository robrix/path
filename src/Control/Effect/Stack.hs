{-# LANGUAGE DeriveFunctor, ExistentialQuantification, StandaloneDeriving #-}
module Control.Effect.Stack where

import Control.Effect.Carrier

data Stack e m k
  = forall a . Push e (m a) (e -> a -> k)
  | Map (e -> e) k

deriving instance Functor (Stack e m)

instance HFunctor (Stack e) where
  hmap f (Push e m k) = Push e (f m) k
  hmap _ (Map f    k) = Map f     k

instance Effect (Stack e) where
  handle state handler (Push e m k) = Push e (handler (m <$ state)) (fmap handler . fmap . k)
  handle state handler (Map f    k) = Map f (handler (k <$ state))
