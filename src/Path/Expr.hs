{-# LANGUAGE DeriveTraversable, LambdaCase, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeOperators #-}
module Path.Expr where

import Control.Monad (ap)
import Data.Coerce (coerce)
import Data.Functor.Const (Const (..))
import Path.Name (Incr (..))

data Expr a
  = Var a
  | Expr (ExprF Expr a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data ExprF f a
  = Lam (f (Incr (f a)))
  | f a :$ f a
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a)) => Eq   (ExprF f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a)) => Ord  (ExprF f a)
deriving instance (Show a, forall a . Show a => Show (f a)) => Show (ExprF f a)

instance Applicative Expr where
  pure = Var
  (<*>) = ap

instance Monad Expr where
  a >>= f = ecata id Expr Var f a


ecata :: forall m n a b
      .  (forall a . m a -> n a)
      -> (forall a . ExprF n a -> n a)
      -> (forall a . Incr (n a) -> m (Incr (n a)))
      -> (a -> m b)
      -> Expr a
      -> n b
ecata var alg k = go
  where go :: forall x y . (x -> m y) -> Expr x -> n y
        go h = \case
          Var a -> var (h a)
          Expr (Lam b) -> alg (Lam (go (k . fmap (go h)) b))
          Expr (f :$ a) -> alg (go h f :$ go h a)

kcata :: (a -> b)
      -> (forall a . ExprF (Const b) a -> b)
      -> (Incr b -> a)
      -> (x -> a)
      -> Expr x
      -> b
kcata var alg k h = getConst . ecata (coerce var) (coerce alg) (coerce k) (Const . h)
