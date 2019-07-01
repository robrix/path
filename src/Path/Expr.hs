{-# LANGUAGE DeriveTraversable, LambdaCase, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving #-}
module Path.Expr where

import Data.Coerce (coerce)
import Data.Functor.Const (Const (..))
import Path.Name (Incr (..), Scope (..), foldScope)

data Expr a
  = Var a
  | Expr (ExprF Expr a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Expr where
  pure = Var
  f <*> a = eiter id Expr Var (<$> a) f

instance Monad Expr where
  a >>= f = eiter id Expr Var f a


data ExprF f a
  = Lam (Scope f a)
  | f a :$ f a
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (ExprF f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (ExprF f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (ExprF f a)


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
          Expr (Lam b) -> alg (Lam (foldScope k go h b))
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
