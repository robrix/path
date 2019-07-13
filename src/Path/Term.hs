{-# LANGUAGE DeriveTraversable, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeOperators, UndecidableInstances #-}
module Path.Term where

import Control.Effect.Carrier
import Control.Effect.Sum
import Data.Coerce
import Data.Functor.Const
import Path.Scope

data Term sig a
  = Var a
  | Term (sig (Term sig) a)

deriving instance ( Eq a
                  , Syntax sig
                  , forall g . Functor g => Functor (sig g)
                  , forall g x . (Eq  x, Monad g, forall y . Eq  y => Eq  (g y)) => Eq  (sig g x)
                  )
               => Eq  (Term sig a)
deriving instance ( Ord a
                  , Syntax sig
                  , forall g . Functor g => Functor (sig g)
                  , forall g x . (Eq  x, Monad g, forall y . Eq  y => Eq  (g y)) => Eq  (sig g x)
                  , forall g x . (Ord x, Monad g, forall y . Eq  y => Eq  (g y)
                                                , forall y . Ord y => Ord (g y)) => Ord (sig g x)
                  )
               => Ord (Term sig a)
deriving instance (Show a, forall g x . (Show x, forall y . Show y => Show (g y)) => Show (sig g x)) => Show (Term sig a)

deriving instance ( forall g . Foldable    g => Foldable    (sig g)) => Foldable    (Term sig)
deriving instance ( forall g . Functor     g => Functor     (sig g)) => Functor     (Term sig)
deriving instance ( forall g . Foldable    g => Foldable    (sig g)
                  , forall g . Functor     g => Functor     (sig g)
                  , forall g . Traversable g => Traversable (sig g)) => Traversable (Term sig)

instance (Syntax sig, forall g . Functor g => Functor (sig g)) => Applicative (Term sig) where
  pure = Var
  f <*> a = iter id Term Var (<$> a) f

instance (Syntax sig, forall g . Functor g => Functor (sig g)) => Monad (Term sig) where
  a >>= f = iter id Term Var f a

instance (Syntax sig, forall g . Functor g => Functor (sig g)) => Carrier sig (Term sig) where
  eff = Term


iter :: forall m n sig a b
     .  Syntax sig
     => (forall a . m a -> n a)
     -> (forall a . sig n a -> n a)
     -> (forall a . Incr () (n a) -> m (Incr () (n a)))
     -> (a -> m b)
     -> Term sig a
     -> n b
iter var alg bound = go
  where go :: forall x y . (x -> m y) -> Term sig x -> n y
        go free = \case
          Var a -> var (free a)
          Term t -> alg (foldSyntax go bound free t)

kcata :: Syntax sig
      => (a -> b)
      -> (forall a . sig (Const b) a -> b)
      -> (Incr () b -> a)
      -> (x -> a)
      -> Term sig x
      -> b
kcata var alg k h = getConst . iter (coerce var) (Const . alg) (coerce k) (Const . h)


class HFunctor sig => Syntax sig where
  foldSyntax :: (forall x y . (x -> m y) -> f x -> n y)
             -> (forall a . Incr () (n a) -> m (Incr () (n a)))
             -> (a -> m b)
             -> sig f a
             -> sig n b

instance Syntax (Scope ()) where
  foldSyntax go bound free = Scope . go (bound . fmap (go free)) . unScope

instance (Syntax l, Syntax r) => Syntax (l :+: r) where
  foldSyntax go bound free (L l) = L (foldSyntax go bound free l)
  foldSyntax go bound free (R r) = R (foldSyntax go bound free r)
