{-# LANGUAGE DeriveAnyClass, DeriveGeneric, DeriveTraversable, DerivingStrategies, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeOperators, UndecidableInstances #-}
module Path.Surface where

import Control.Applicative
import Control.Effect.Carrier
import Control.Effect.Interpret
import Control.Effect.Reader
import Control.Monad (join)
import Control.Monad.Module
import Control.Monad.Trans
import GHC.Generics (Generic1)
import Path.Name
import Path.Plicity
import Path.Scope
import Path.Span
import Path.Syntax
import Path.Term
import Path.Usage

data Surface f a
  = Lam (Plicit (Ignored (Maybe User))) (Spanned (Scope () f a))
  | Spanned (f a) :$ Plicit (Spanned (f a))
  | Type
  | Pi (Plicit (Ignored (Maybe User) ::: Used (Spanned (f a)))) (Spanned (Scope () f a))
  deriving (Foldable, Functor, Generic1, HFunctor, Traversable)

deriving instance (Eq   a, forall a . Eq   a => Eq   (f a), Monad f) => Eq   (Surface f a)
deriving instance (Ord  a, forall a . Eq   a => Eq   (f a)
                         , forall a . Ord  a => Ord  (f a), Monad f) => Ord  (Surface f a)
deriving instance (Show a, forall a . Show a => Show (f a))          => Show (Surface f a)

instance RightModule Surface where
  Lam p b >>=* f = Lam p (fmap (>>=* f) b)
  g :$ a  >>=* f = (fmap (>>= f) g) :$ (fmap (fmap (>>= f)) a)
  Type    >>=* _ = Type
  Pi t b  >>=* f = Pi (fmap (fmap (fmap (fmap (>>= f)))) t) (fmap (>>=* f) b)

instance Syntax Surface where
  foldSyntax go bound free = \case
    Lam p b -> Lam p (foldSyntax go bound free <$> b)
    f :$ a -> (go free <$> f) :$ (fmap (go free) <$> a)
    Type -> Type
    Pi t b -> Pi (fmap (fmap (fmap (go free))) <$> t) (foldSyntax go bound free <$> b)

newtype SurfaceC m a = SurfaceC { runSurfaceC :: m (Term Surface a) }
  deriving (Functor)

instance Applicative m => Applicative (SurfaceC m) where
  pure = SurfaceC . pure . Var
  SurfaceC f <*> SurfaceC a = SurfaceC (liftA2 (<*>) f a)

instance Monad m => Monad (SurfaceC m) where
  -- FIXME: is this valid?
  SurfaceC m >>= f = SurfaceC (m >>= fmap join . traverse (runSurfaceC . f))

instance (Carrier sig m, Effect sig) => Carrier (Surface :+: sig) (SurfaceC m) where
  eff (L s) = SurfaceC . fmap Term $ case s of
    f :$ a -> (:$) <$> traverse runSurfaceC f <*> traverse (traverse runSurfaceC) a
    Lam p b -> Lam p <$> traverse recur b
    Type -> pure Type
    Pi t b -> Pi <$> traverse (traverse (traverse (traverse runSurfaceC))) t <*> traverse recur b
    where recur = fmap Scope . (>>= traverse (traverse runSurfaceC)) . runSurfaceC . unScope
  -- FIXME: is this valid?
  eff (R other) = SurfaceC (eff (handle (Var ()) (fmap join . traverse runSurfaceC) other))


lam :: (Eq a, Carrier sig m, Member Surface sig) => Plicit (Named (Maybe User) a) -> Spanned (m a) -> m a
lam (p :< Named u n) b = send (Lam (p :< u) (bind1 n <$> b))

lam' :: (Carrier sig m, Member Surface sig) => Plicit (Maybe User) -> Spanned (m User) -> m User
lam' (p :< Nothing) b = send (Lam (p :< Ignored Nothing) (lift <$> b))
lam' (p :< Just n)  b = lam (p :< named (Just n) n) b

($$) :: (Carrier sig m, Member Surface sig) => Spanned (m a) -> Plicit (Spanned (m a)) -> m a
f $$ a = send (f :$ a)


type' :: (Carrier sig m, Member Surface sig) => m a
type' = send Type

pi :: (Eq a, Carrier sig m, Member Surface sig) => Plicit (Named (Maybe User) a ::: Used (Spanned (m a))) -> Spanned (m a) -> m a
pi (p :< Named u n ::: t) b = send (Pi (p :< u ::: t) (bind1 n <$> b))

(-->) :: (Carrier sig m, Member Surface sig) => Used (Spanned (m a)) -> Spanned (m a) -> m a
t --> b = send (Pi (Ex :< Ignored Nothing ::: t) (lift <$> b))

infixr 0 -->


-- | Decorate a term’s variables with the most local
decorate :: Spanned (Term Surface a) -> Spanned (Term Surface (Spanned a))
decorate (a :~ s) = runReader s (walk (asks . (:~)) a) :~ s

walk :: (Carrier sig m, Member (Reader Span) sig, Member Surface sig)
     => (a -> m b)
     -> Term Surface a
     -> m b
walk k = (>>= k) . runInterpret alg . interpret
  where alg = \case
          Lam p b -> send (Lam p (Scope <$> withSpan (unScope <$> b)))
          f :$ a -> withSpan f $$ fmap withSpan a
          Type -> type'
          Pi t b -> send (Pi (fmap (fmap withSpan) <$> t) (Scope <$> withSpan (unScope <$> b)))
        withSpan s = spanIs s <$ s
