{-# LANGUAGE DeriveTraversable, LambdaCase, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeOperators #-}
module Path.Expr where

import Control.Monad (ap)
import Data.Coerce (coerce)
import Data.Functor.Const (Const (..))
import Path.Name (Incr (..))

newtype Expr a = Expr { unExpr :: ExprF Expr a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data ExprF f a
  = Var a
  | Lam (f (Incr (f a)))
  | f a :$ f a
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a)) => Eq   (ExprF f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a)) => Ord  (ExprF f a)
deriving instance (Show a, forall a . Show a => Show (f a)) => Show (ExprF f a)

instance Applicative Expr where
  pure = Expr . Var
  (<*>) = ap

instance Monad Expr where
  a >>= f = efold id (Expr . Lam) (fmap Expr . (:$)) pure f a


efold :: forall m n incr a b
      .  (forall a . m a -> n a)
      -> (forall a . n (incr (n a)) -> n a)
      -> (forall a . n a -> n a -> n a)
      -> (forall a . Incr (n a) -> m (incr (n a)))
      -> (a -> m b)
      -> Expr a
      -> n b
efold var lam app k = go
  where go :: forall x y . (x -> m y) -> Expr x -> n y
        go h = \case
          Expr (Var a) -> var (h a)
          Expr (Lam b) -> lam (go (k . fmap (go h)) b)
          Expr (f :$ a) -> go h f `app` go h a

kfold :: (a -> b)
      -> (b -> b)
      -> (b -> b -> b)
      -> (Incr b -> a)
      -> (x -> a)
      -> Expr x
      -> b
kfold var lam app k h = getConst . efold (coerce var) (coerce lam) (coerce app) (coerce k) (Const . h)
