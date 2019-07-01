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
  a >>= f = efold id (\ p -> Core . Lam p) (fmap Core . (:$)) (Core Type) (\ t -> Core . Pi t) (Core . Hole) (fmap Core . Ann) pure f a


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


lam :: Eq a => Plicit a -> Core a -> Core a
lam (p :< n) b = Core (Lam (p :< Nothing) (bind n b))

lams :: (Eq a, Foldable t) => t (Plicit a) -> Core a -> Core a
lams names body = foldr lam body names


efold :: forall m n a b
      .  (forall a . m a -> n a)
      -> (forall a . Plicit (Maybe User) -> Scope n a -> n a)
      -> (forall a . n a -> Plicit (n a) -> n a)
      -> (forall a . n a)
      -> (forall a . Plicit (Maybe User ::: Used (n a)) -> Scope n a -> n a)
      -> (forall a . Gensym -> n a)
      -> (forall a . Span -> n a -> n a)
      -> (forall a . Incr (n a) -> m (Incr (n a)))
      -> (a -> m b)
      -> Core a
      -> n b
efold var lam app ty pi hole ann k = go
  where go :: forall x y . (x -> m y) -> Core x -> n y
        go h = \case
          Var a -> var (h a)
          Core c -> case c of
            Lam p (Scope b) -> lam p (Scope (go (k . fmap (go h)) b))
            f :$ a -> app (go h f) (go h <$> a)
            Type -> ty
            Pi t (Scope b) -> pi (fmap (fmap (go h)) <$> t) (Scope (go (k . fmap (go h)) b))
            Hole a -> hole a
            Ann loc b -> ann loc (go h b)
