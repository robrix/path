{-# LANGUAGE DeriveTraversable, LambdaCase, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeOperators #-}
module Path.Surface where

import Control.Monad.Trans
import Path.Name
import Path.Plicity
import Path.Usage
import Text.Trifecta.Rendering (Spanned)

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
  = Lam (Plicit (Maybe User)) (Spanned (Scope f a))
  | Spanned (f a) :$ Plicit (Spanned (f a))
  | Type
  | Pi (Plicit (Maybe User ::: Used (Spanned (f a)))) (Spanned (Scope f a))
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (SurfaceF f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (SurfaceF f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (SurfaceF f a)


lam :: Eq a => Plicit (Maybe User, a) -> Spanned (Surface a) -> Surface a
lam (p :< (u, n)) b = Surface (Lam (p :< u) (bind n <$> b))

lam' :: Plicit (Maybe User) -> Spanned (Surface Var) -> Surface Var
lam' (p :< Nothing) b = Surface (Lam (p :< Nothing) (lift <$> b))
lam' (p :< Just n)  b = lam (p :< (Just n, U n)) b

($$) :: Spanned (Surface a) -> Plicit (Spanned (Surface a)) -> Surface a
f $$ a = Surface (f :$ a)


type' :: Surface a
type' = Surface Type

pi :: Eq a => Plicit ((Maybe User, a) ::: Used (Spanned (Surface a))) -> Spanned (Surface a) -> Surface a
pi (p :< (u, n) ::: t) b = Surface (Pi (p :< u ::: t) (bind n <$> b))

(-->) :: Used (Spanned (Surface a)) -> Spanned (Surface a) -> Surface a
t --> b = Surface (Pi (Ex :< Nothing ::: t) (lift <$> b))

infixr 0 -->


eiter :: forall m n a b
      .  (forall a . m a -> n a)
      -> (forall a . SurfaceF n a -> n a)
      -> (forall a . Incr (n a) -> m (Incr (n a)))
      -> (a -> m b)
      -> Surface a
      -> n b
eiter var alg k = go
  where go :: forall x y . (x -> m y) -> Surface x -> n y
        go h = \case
          Var a -> var (h a)
          Surface s -> case s of
            Lam p b -> alg (Lam p (foldScope k go h <$> b))
            f :$ a -> alg ((go h <$> f) :$ (fmap (go h) <$> a))
            Type -> alg Type
            Pi t b -> alg (Pi (fmap (fmap (fmap (go h))) <$> t) (foldScope k go h <$> b))
