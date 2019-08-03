{-# LANGUAGE DeriveTraversable, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, UndecidableInstances #-}
module Path.Term where

import Control.Effect.Carrier
import Control.Monad (ap)
import Control.Monad.Module
import Path.Pretty
import Path.Scope

data Term sig a
  = Var a
  | Term (sig (Term sig) a)

deriving instance ( Eq a
                  , RightModule sig
                  , forall g x . (Eq  x, Monad g, forall y . Eq  y => Eq  (g y)) => Eq  (sig g x)
                  )
               => Eq  (Term sig a)
deriving instance ( Ord a
                  , RightModule sig
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

instance RightModule sig => Applicative (Term sig) where
  pure = Var
  (<*>) = ap

instance RightModule sig => Monad (Term sig) where
  Var  a >>= f = f a
  Term t >>= f = Term (t >>=* f)

instance RightModule sig => Carrier sig (Term sig) where
  eff = Term


hoistTerm
  :: forall sig sig' a
  .  ( HFunctor sig
     , forall g . Functor g => Functor (sig g)
     )
  => (forall m x . sig m x -> sig' m x)
  -> Term sig a
  -> Term sig' a
hoistTerm f = go
  where go :: Term sig x -> Term sig' x
        go = \case
          Var v  -> Var v
          Term t -> Term (f (hmap go t))


prettyTerm
  :: forall sig a
  .  (forall g . Foldable g => Foldable (sig g), Pretty a, RightModule sig)
  => (forall f n . (Foldable f, Monad f) => (forall n . Vec n Doc -> f (Var (Fin n) a) -> Prec) -> Vec n Doc -> sig f (Var (Fin n) a) -> Prec)
  -> Term sig a
  -> Doc
prettyTerm alg = precDoc . prettyTermInContext alg VZ . fmap F

prettyTermInContext
  :: forall sig n a
  .  (forall g . Foldable g => Foldable (sig g), Pretty a, RightModule sig)
  => (forall f n . (Foldable f, Monad f) => (forall n . Vec n Doc -> f (Var (Fin n) a) -> Prec) -> Vec n Doc -> sig f (Var (Fin n) a) -> Prec)
  -> Vec n Doc
  -> Term sig (Var (Fin n) a)
  -> Prec
prettyTermInContext alg = go
  where go :: forall n . Vec n Doc -> Term sig (Var (Fin n) a) -> Prec
        go ctx = \case
          Var v -> atom (var (ctx !) pretty v)
          Term t -> alg go ctx t
