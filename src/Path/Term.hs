{-# LANGUAGE DeriveTraversable, FlexibleInstances, MultiParamTypeClasses, QuantifiedConstraints, StandaloneDeriving, UndecidableInstances #-}
module Path.Term where

import Control.Effect.Carrier
import Control.Monad (ap)
import Control.Monad.Module
import Data.Void

data Term f a
  = Var a
  | Term (f (Term f) a)

deriving instance (Eq   a, Eq   (f (Term f) a)) => Eq   (Term f a)
deriving instance (Ord  a, Ord  (f (Term f) a)) => Ord  (Term f a)
deriving instance (Show a, Show (f (Term f) a)) => Show (Term f a)

deriving instance (forall g . Foldable    g => Foldable    (f g)) => Foldable    (Term f)
deriving instance (forall g . Functor     g => Functor     (f g)) => Functor     (Term f)
deriving instance (forall g . Foldable    g => Foldable    (f g)
                 , forall g . Functor     g => Functor     (f g)
                 , forall g . Traversable g => Traversable (f g)) => Traversable (Term f)

type Closed f = Term f Void


instance (forall g . Functor g => Functor (f g), forall g . RModule (f g) g) => Applicative (Term f) where
  pure = Var
  (<*>) = ap

instance (forall g . Functor g => Functor (f g), forall g . RModule (f g) g) => Monad (Term f) where
  Var a  >>= f = f a
  Term g >>= f = Term (g >>=* f)

instance (forall g . Functor g => Functor (f g), forall g . RModule (f g) g, HFunctor f) => Carrier f (Term f) where
  eff = Term
