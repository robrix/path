{-# LANGUAGE DeriveAnyClass, DeriveGeneric, DeriveTraversable, DerivingStrategies, FlexibleContexts, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeOperators #-}
module Path.Surface where

import Control.Applicative
import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Reader
import Control.Monad (guard, join)
import Control.Monad.Trans
import Data.Coerce
import GHC.Generics ((:.:) (..), Generic1)
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

instance Carrier SurfaceF Surface where
  eff = Surface

data SurfaceF f a
  = Lam (Plicit (Ignored (Maybe User))) (Spanned (Scope (Ignored (Maybe User)) f a))
  | Spanned (f a) :$ Plicit (Spanned (f a))
  | Type
  | Pi (Plicit (Ignored (Maybe User) ::: Used (Spanned (f a)))) (Spanned (Scope (Ignored (Maybe User)) f a))
  deriving (Foldable, Functor, Generic1, HFunctor, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (SurfaceF f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (SurfaceF f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (SurfaceF f a)

newtype SurfaceC m a = SurfaceC { runSurfaceC :: m (Surface a) }
  deriving (Functor)

instance Applicative m => Applicative (SurfaceC m) where
  pure = SurfaceC . pure . Var
  SurfaceC f <*> SurfaceC a = SurfaceC (liftA2 (<*>) f a)

instance Monad m => Monad (SurfaceC m) where
  -- FIXME: is this valid?
  SurfaceC m >>= f = SurfaceC (m >>= fmap join . traverse (runSurfaceC . f))


lam :: Eq a => Plicit (Named (Maybe User) a) -> Spanned (Surface a) -> Surface a
lam (p :< Named u n) b = Surface (Lam (p :< u) (bind ((u <$) . guard . (== n)) <$> b))

lam' :: Plicit (Maybe User) -> Spanned (Surface User) -> Surface User
lam' (p :< Nothing) b = Surface (Lam (p :< Ignored Nothing) (lift <$> b))
lam' (p :< Just n)  b = lam (p :< named (Just n) n) b

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
        go free = \case
          Var a -> var (free a)
          Surface s -> alg $ case s of
            Lam p b -> Lam p (foldScope k go free <$> b)
            f :$ a -> (go free <$> f) :$ (fmap (go free) <$> a)
            Type -> Type
            Pi t b -> Pi (fmap (fmap (fmap (go free))) <$> t) (foldScope k go free <$> b)

kcata :: (a -> b)
      -> (forall a . SurfaceF (Const b) a -> b)
      -> (Incr (Ignored (Maybe User)) b -> a)
      -> (x -> a)
      -> Surface x
      -> b
kcata var alg k free = getConst . eiter (coerce var) (coerce alg) (coerce k) (Const . free)


-- | Decorate a term’s variables with the most local
decorate :: forall a . Spanned (Surface a) -> Surface (Spanned a)
decorate (a :~ s) = run (runReader s (walk (asks . (:~)) a))

walk :: (Carrier sig m, Member (Reader Span) sig)
     => (a -> m b)
     -> Surface a
     -> m (Surface b)
walk k = unComp1 . eiter (Comp1 . fmap Var) alg pure k
  where alg = Comp1 . fmap Surface . \case
          Lam p b -> Lam p <$> withSpan recur b
          f :$ a -> (:$) <$> withSpan unComp1 f <*> traverse (withSpan unComp1) a
          Type -> pure Type
          Pi t b -> Pi <$> traverse (traverse (traverse (withSpan unComp1))) t <*> withSpan recur b
        recur = fmap Scope . (>>= traverse (traverse unComp1)) . unComp1 . unScope
        withSpan recur (t :~ s) = (:~ s) <$> local (const s) (recur t)
