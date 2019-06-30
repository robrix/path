{-# LANGUAGE DeriveTraversable, LambdaCase, RankNTypes, ScopedTypeVariables, TypeOperators #-}
module Path.Expr where

import Control.Monad (ap)
import Data.Coerce (coerce)
import Data.Functor.Const (Const (..))
import Path.Name (Incr (..))

data Expr a
  = Var a
  | Lam (Expr (Incr (Expr a)))
  | Expr a :$ Expr a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Expr where
  pure = Var
  (<*>) = ap

instance Monad Expr where
  a >>= f = efold id Lam (:$) Var f a


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
          Var a -> var (h a)
          Lam b -> lam (go (k . fmap (go h)) b)
          f :$ a -> go h f `app` go h a

kfold :: (a -> b)
      -> (b -> b)
      -> (b -> b -> b)
      -> (Incr b -> a)
      -> (x -> a)
      -> Expr x
      -> b
kfold var lam app k h = getConst . efold (coerce var) (coerce lam) (coerce app) (coerce k) (Const . h)
