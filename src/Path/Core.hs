{-# LANGUAGE DeriveTraversable, LambdaCase, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeOperators #-}
module Path.Core where

import Control.Monad (ap)
import Path.Name
import Path.Plicity
import Path.Usage
import Prelude hiding (pi)
import Text.Trifecta.Rendering (Span)

data Core a
  = Var a
  | Core (CoreF Core a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Core where
  pure = Var
  (<*>) = ap

instance Monad Core where
  a >>= f = eiter id Core pure f a


data CoreF f a
  = Lam (Plicit (Maybe User)) (Scope f a)
  | f a :$ Plicit (f a)
  | Type
  | Pi (Plicit (Maybe User ::: Used (f a))) (Scope f a)
  | Hole Gensym
  | Ann Span (f a)
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (CoreF f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (CoreF f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (CoreF f a)


lam :: Eq a => Plicit (Maybe User, a) -> Core a -> Core a
lam (p :< (u, n)) b = Core (Lam (p :< u) (bind n b))

lams :: (Eq a, Foldable t) => t (Plicit (Maybe User, a)) -> Core a -> Core a
lams names body = foldr lam body names


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
            Lam p b -> alg (Lam p (foldScope k go h b))
            f :$ a -> alg (go h f :$ (go h <$> a))
            Type -> alg Type
            Pi t b -> alg (Pi (fmap (fmap (go h)) <$> t) (foldScope k go h b))
            Hole a -> alg (Hole a)
            Ann loc b -> alg (Ann loc (go h b))
