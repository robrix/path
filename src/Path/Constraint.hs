{-# LANGUAGE DeriveFunctor, ExistentialQuantification, GADTs, LambdaCase, StandaloneDeriving #-}
module Path.Constraint where

data Constraint a where
  Top :: Constraint ()
  (:/\:) :: Constraint a -> Constraint b -> Constraint (a, b)
  (:=:) :: Int -> Int -> Constraint ()

data Witness a where
  WUnit :: Witness ()
  WConj :: Witness a -> Witness b -> Witness (a, b)

data Solver m a = forall b . Solver (Constraint b) (Witness b -> m a)

deriving instance Functor m => Functor (Solver m)

instance Applicative m => Applicative (Solver m) where
  pure a = Solver Top (const (pure a))

  Solver c1 f <*> Solver c2 a = Solver (c1 :/\: c2) (\case
    WConj wf wa -> f wf <*> a wa)
