{-# LANGUAGE DeriveFunctor, ExistentialQuantification, FlexibleContexts, StandaloneDeriving #-}
module Control.Effect.Stack where

import Control.Effect.Carrier
import Control.Effect.Sum

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


push :: (Carrier sig m, Member (Stack e) sig) => e -> m a -> m (e, a)
push e m = send (Push e m (curry pure))
