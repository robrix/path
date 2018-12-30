{-# LANGUAGE DeriveFunctor, FlexibleContexts, KindSignatures #-}
module Path.Constraint where

import Control.Effect.Carrier
import Control.Effect.Sum
import Data.Coerce

newtype MetaVar = M Int
  deriving (Eq, Ord, Show)

data Solver (m :: * -> *) a
  = Unify MetaVar MetaVar a
  deriving (Functor)

instance HFunctor Solver where
  hmap _ = coerce

instance Effect Solver where
  handle state handler = coerce . fmap (handler . (<$ state))


(~~) :: (Carrier sig m, Member Solver sig) => MetaVar -> MetaVar -> m ()
m1 ~~ m2 = send (Unify m1 m2 (ret ()))
