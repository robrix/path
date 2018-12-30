{-# LANGUAGE DeriveFunctor, KindSignatures #-}
module Path.Constraint where

newtype MetaVar = M Int
  deriving (Eq, Ord, Show)

data Solver (m :: * -> *) a
  = Unify MetaVar MetaVar a
  deriving (Functor)
