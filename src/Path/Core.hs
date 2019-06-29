{-# LANGUAGE DeriveTraversable, LambdaCase, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, TypeOperators #-}
module Path.Core where

import Control.Monad (ap)
import Data.Coerce
import GHC.Generics ((:.:) (..))
import Path.Name
import Path.Plicity
import Path.Usage
import Prelude hiding (pi)
import Text.Trifecta.Rendering (Span)

data Core a
  = Var (Name a)
  | Lam (Plicit (Maybe User)) (Core (Incr (Core a)))
  | Core a :$ Plicit (Core a)
  | Type
  | Pi Usage (Core a) (Core a)
  | Hole Gensym
  | Ann Span (Core a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Core where
  pure = Var . Local
  (<*>) = ap

instance Monad Core where
  a >>= f = gfold (name id (Var . Global)) Lam (:$) Type Pi Hole Ann pure (fmap f a)

lam :: Eq a => Plicit a -> Core a -> Core a
lam (p :< n) b = Lam (p :< Nothing) (bind n b)

lams :: (Eq a, Foldable t) => t (Plicit a) -> Core a -> Core a
lams names body = foldr lam body names


gfold :: forall m n b
      .  (forall a . Name (m a) -> n a)
      -> (forall a . Plicit (Maybe User) -> n (Incr (n a)) -> n a)
      -> (forall a . n a -> Plicit (n a) -> n a)
      -> (forall a . n a)
      -> (forall a . Usage -> n a -> n a -> n a)
      -> (forall a . Gensym -> n a)
      -> (forall a . Span -> n a -> n a)
      -> (forall a . Incr (n a) -> m (Incr (n a)))
      -> Core (m b)
      -> n b
gfold var lam app ty pi hole ann k = go
  where go :: Core (m x) -> n x
        go = \case
          Var a -> var a
          Lam n b -> lam n (go (k . fmap go <$> b))
          f :$ a -> app (go f) (go <$> a)
          Type -> ty
          Pi m t b -> pi m (go t) (go b)
          Hole a -> hole a
          Ann span a -> ann span (go a)

efold :: forall l m n z b
      .  ( forall a b . Coercible a b => Coercible (n a) (n b)
         , forall a b . Coercible a b => Coercible (m a) (m b)
         )
      => (forall a . Name (m a) -> n a)
      -> (forall a . Plicit (Maybe User) -> n (Incr (n a)) -> n a)
      -> (forall a . n a -> Plicit (n a) -> n a)
      -> (forall a . n a)
      -> (forall a . Usage -> n a -> n a -> n a)
      -> (forall a . Gensym -> n a)
      -> (forall a . Span -> n a -> n a)
      -> (forall a . Incr (n a) -> m (Incr (n a)))
      -> (l b -> m (z b))
      -> Core (l b)
      -> n (z b)
efold var lam app ty pi hole ann k = go
  where go :: forall l' z' x . (l' x -> m (z' x)) -> Core (l' x) -> n (z' x)
        go h = \case
          Var a -> var (h <$> a)
          Lam p b -> lam p (coerce (go
                       (coerce (k . fmap (go h))
                         :: ((Incr :.: Core :.: l') x -> m ((Incr :.: n :.: z') x)))
                       (coerce b)))
          f :$ a -> app (go h f) (go h <$> a)
          Type -> ty
          Pi m t b -> pi m (go h t) (go h b)
          Hole a -> hole a
          Ann loc b -> ann loc (go h b)
