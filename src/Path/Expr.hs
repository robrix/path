{-# LANGUAGE DeriveTraversable, LambdaCase, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving #-}
module Path.Expr where

import Control.Monad (ap)
import Data.Coerce (coerce)
import Data.Functor.Const (Const (..))
import Path.Name (Incr (..), flatten)

data Expr a
  = Var a
  | Expr (ExprF Expr a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data ExprF f a
  = Lam (f (Incr (f a)))
  | f a :$ f a
  deriving (Foldable, Functor, Traversable)

instance (Monad f, Eq  a, forall a . Eq  a => Eq  (f a)) => Eq (ExprF f a) where
  Lam b1   == Lam b2   = flatten b1 == flatten b2
  f1 :$ a1 == f2 :$ a2 = f1 == f2 && a1 == a2
  _        == _        = False

instance (Monad f, Ord a, forall a . Eq  a => Eq  (f a)
                        , forall a . Ord a => Ord (f a)) => Ord (ExprF f a) where
  Lam b1     `compare` Lam b2     = flatten b1 `compare` flatten b2
  Lam _      `compare` _          = LT
  _          `compare` Lam _      = GT
  (f1 :$ a1) `compare` (f2 :$ a2) = f1 `compare` f2 <> a1 `compare` a2

deriving instance (Show a, forall a . Show a => Show (f a)) => Show (ExprF f a)

instance Applicative Expr where
  pure = Var
  (<*>) = ap

instance Monad Expr where
  a >>= f = eiter id Expr Var f a


eiter :: forall m n a b
      .  (forall a . m a -> n a)
      -> (forall a . ExprF n a -> n a)
      -> (forall a . Incr (n a) -> m (Incr (n a)))
      -> (a -> m b)
      -> Expr a
      -> n b
eiter var alg k = go
  where go :: forall x y . (x -> m y) -> Expr x -> n y
        go h = \case
          Var a -> var (h a)
          Expr (Lam b) -> alg (Lam (go (k . fmap (go h)) b))
          Expr (f :$ a) -> alg (go h f :$ go h a)

ecata :: (forall a . ExprF m a -> m a)
      -> (forall a . Incr (m a) -> m (Incr (m a)))
      -> Expr (m a)
      -> m a
ecata alg k = eiter id alg k id

kcata :: (a -> b)
      -> (forall a . ExprF (Const b) a -> b)
      -> (Incr b -> a)
      -> (x -> a)
      -> Expr x
      -> b
kcata var alg k h = getConst . eiter (coerce var) (coerce alg) (coerce k) (Const . h)
