{-# LANGUAGE DeriveFunctor, ExistentialQuantification, FlexibleContexts, GADTs, LambdaCase, StandaloneDeriving #-}
module Path.Constraint where

import Path.Context
import Path.Name

data Constraint a where
  Top :: Constraint ()
  (:/\:) :: Constraint a -> Constraint b -> Constraint (a, b)
  (:==:) :: Int -> Int -> Constraint ()
  Instance :: QName -> Int -> Constraint [Type QName]

data Witness a where
  WUnit :: Witness ()
  WConj :: Witness a -> Witness b -> Witness (a, b)
  WInst :: [Type QName] -> Witness [Type QName]

data Solver m a = forall b . Solver (m (Constraint b, Witness b -> m a))

(~~) :: Applicative m => Int -> Int -> Solver m ()
v1 ~~ v2 = Solver (pure (v1 :==: v2, const (pure ())))

instance' :: Applicative m => QName -> Int -> Solver m [Type QName]
instance' x v = Solver (pure (Instance x v, \case
  WInst tys -> pure tys))

deriving instance Functor m => Functor (Solver m)

instance Applicative m => Applicative (Solver m) where
  pure a = Solver (pure (Top, const (pure a)))

  Solver f <*> Solver a = Solver (combine <$> f <*> a)
    where combine :: Applicative m => (Constraint x, Witness x -> m (a -> b)) -> (Constraint y, Witness y -> m a) -> (Constraint (x, y), Witness (x, y) -> m b)
          combine (c1, f') (c2, a') = (c1 :/\: c2, \case
            WConj wf wa -> f' wf <*> a' wa)
