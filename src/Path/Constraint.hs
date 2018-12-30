{-# LANGUAGE DeriveFunctor, ExistentialQuantification, GADTs, LambdaCase, StandaloneDeriving #-}
module Path.Constraint where

import Path.Context
import Path.Name

data Constraint a where
  Top :: Constraint ()
  (:/\:) :: Constraint a -> Constraint b -> Constraint (a, b)
  (:=:) :: Int -> Int -> Constraint ()
  Instance :: QName -> Int -> Constraint [Type QName]

data Witness a where
  WUnit :: Witness ()
  WConj :: Witness a -> Witness b -> Witness (a, b)
  WInst :: [Type QName] -> Witness [Type QName]

data Solver m a = forall b . Solver (Constraint b) (Witness b -> m a)

instance' :: Applicative m => QName -> Int -> Solver m [Type QName]
instance' x v = Solver (Instance x v) (\case
  WInst tys -> pure tys)

deriving instance Functor m => Functor (Solver m)

instance Applicative m => Applicative (Solver m) where
  pure a = Solver Top (const (pure a))

  Solver c1 f <*> Solver c2 a = Solver (c1 :/\: c2) (\case
    WConj wf wa -> f wf <*> a wa)
