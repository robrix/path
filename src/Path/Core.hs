{-# LANGUAGE DeriveTraversable, LambdaCase, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeOperators #-}
module Path.Core where

import Path.Name
import Path.Plicity
import Path.Usage
import Prelude hiding (pi)
import Text.Trifecta.Rendering (Spanned)

data Core a
  = Var a
  | Core (CoreF Core a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Core where
  pure = Var
  f <*> a = eiter id Core Var (<$> a) f

instance Monad Core where
  a >>= f = eiter id Core Var f a


data CoreF f a
  = Lam (Plicit (Maybe User)) (Spanned (Scope f a))
  | Spanned (f a) :$ Plicit (Spanned (f a))
  | Type
  | Pi (Plicit (Maybe User ::: Used (Spanned (f a)))) (Spanned (Scope f a))
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (CoreF f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (CoreF f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (CoreF f a)


eiter :: forall m n a b
      .  (forall a . m a -> n a)
      -> (forall a . CoreF n a -> n a)
      -> (forall a . Incr (n a) -> m (Incr (n a)))
      -> (a -> m b)
      -> Core a
      -> n b
eiter var alg k = go
  where go :: forall x y . (x -> m y) -> Core x -> n y
        go h = \case
          Var a -> var (h a)
          Core c -> case c of
            Lam p b -> alg (Lam p (foldScope k go h <$> b))
            f :$ a -> alg ((go h <$> f) :$ (fmap (go h) <$> a))
            Type -> alg Type
            Pi t b -> alg (Pi (fmap (fmap (fmap (go h))) <$> t) (foldScope k go h <$> b))
