{-# LANGUAGE DeriveTraversable, LambdaCase, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeOperators #-}
module Path.Surface where

import Control.Monad (guard)
import Control.Monad.Trans
import Path.Name
import Path.Plicity
import Path.Scope
import Path.Span
import Path.Usage

data Surface a
  = Var a
  | Surface (SurfaceF Surface a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Surface where
  pure = Var
  f <*> a = eiter id Surface Var (<$> a) f

instance Monad Surface where
  a >>= f = eiter id Surface Var f a

data SurfaceF f a
  = Lam (Plicit (Ignored (Maybe User))) (Spanned (Scope (Ignored (Maybe User)) f a))
  | Spanned (f a) :$ Plicit (Spanned (f a))
  | Type
  | Pi (Plicit (Ignored (Maybe User) ::: Used (Spanned (f a)))) (Spanned (Scope (Ignored (Maybe User)) f a))
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (SurfaceF f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (SurfaceF f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (SurfaceF f a)


lam :: Eq a => Plicit (Named (Maybe User) a) -> Spanned (Surface a) -> Surface a
lam (p :< Named u n) b = Surface (Lam (p :< u) (bind ((u <$) . guard . (== n)) <$> b))

lam' :: Plicit (Maybe User) -> Spanned (Surface Var) -> Surface Var
lam' (p :< Nothing) b = Surface (Lam (p :< Ignored Nothing) (lift <$> b))
lam' (p :< Just n)  b = lam (p :< named (Just n) (U n)) b

($$) :: Spanned (Surface a) -> Plicit (Spanned (Surface a)) -> Surface a
f $$ a = Surface (f :$ a)


type' :: Surface a
type' = Surface Type

pi :: Eq a => Plicit (Named (Maybe User) a ::: Used (Spanned (Surface a))) -> Spanned (Surface a) -> Surface a
pi (p :< Named u n ::: t) b = Surface (Pi (p :< u ::: t) (bind ((u <$) . guard . (== n)) <$> b))

(-->) :: Used (Spanned (Surface a)) -> Spanned (Surface a) -> Surface a
t --> b = Surface (Pi (Ex :< Ignored Nothing ::: t) (lift <$> b))

infixr 0 -->


eiter :: forall m n a b
      .  (forall a . m a -> n a)
      -> (forall a . SurfaceF n a -> n a)
      -> (forall a . Incr (Ignored (Maybe User)) (n a) -> m (Incr (Ignored (Maybe User)) (n a)))
      -> (a -> m b)
      -> Surface a
      -> n b
eiter var alg k = go
  where go :: forall x y . (x -> m y) -> Surface x -> n y
        go h = \case
          Var a -> var (h a)
          Surface s -> alg $ case s of
            Lam p b -> Lam p (foldScope k go h <$> b)
            f :$ a -> (go h <$> f) :$ (fmap (go h) <$> a)
            Type -> Type
            Pi t b -> Pi (fmap (fmap (fmap (go h))) <$> t) (foldScope k go h <$> b)
