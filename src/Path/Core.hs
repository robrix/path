{-# LANGUAGE DeriveTraversable, LambdaCase, RankNTypes, ScopedTypeVariables, TypeOperators #-}
module Path.Core where

import Control.Monad (ap)
import Path.Name
import Path.Plicity
import Path.Usage
import Prelude hiding (pi)
import Text.Trifecta.Rendering (Span)

data Core a
  = Var a
  | Lam (Plicit (Maybe User)) (Core (Incr (Core a)))
  | Core a :$ Plicit (Core a)
  | Type
  | Pi (Plicit (Maybe User ::: Used (Core a))) (Core (Incr (Core a)))
  | Hole Gensym
  | Ann Span (Core a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Core where
  pure = Var
  (<*>) = ap

instance Monad Core where
  a >>= f = efold id Lam (:$) Type Pi Hole Ann pure f a

lam :: Eq a => Plicit a -> Core a -> Core a
lam (p :< n) b = Lam (p :< Nothing) (bind n b)

lams :: (Eq a, Foldable t) => t (Plicit a) -> Core a -> Core a
lams names body = foldr lam body names


efold :: forall m n incr a b
      .  (forall a . m a -> n a)
      -> (forall a . Plicit (Maybe User) -> n (incr (n a)) -> n a)
      -> (forall a . n a -> Plicit (n a) -> n a)
      -> (forall a . n a)
      -> (forall a . Plicit (Maybe User ::: Used (n a)) -> n (incr (n a)) -> n a)
      -> (forall a . Gensym -> n a)
      -> (forall a . Span -> n a -> n a)
      -> (forall a . Incr (n a) -> m (incr (n a)))
      -> (a -> m b)
      -> Core a
      -> n b
efold var lam app ty pi hole ann k = go
  where go :: forall x y . (x -> m y) -> Core x -> n y
        go h = \case
          Var a -> var (h a)
          Lam p b -> lam p (go (k . fmap (go h)) b)
          f :$ a -> app (go h f) (go h <$> a)
          Type -> ty
          Pi t b -> pi (fmap (fmap (go h)) <$> t) (go (k . fmap (go h)) b)
          Hole a -> hole a
          Ann loc b -> ann loc (go h b)
