{-# LANGUAGE DeriveFunctor, KindSignatures #-}
module Path.Constraint where

import Control.Effect.Carrier
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
