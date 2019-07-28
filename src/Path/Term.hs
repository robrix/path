{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeApplications, UndecidableInstances #-}
module Path.Term where

import Control.Effect.Carrier
import Control.Effect.Reader
import Control.Effect.Writer
import Control.Monad (ap)
import Control.Monad.Module
import qualified Data.Set as Set
import Path.Name
import Path.Pretty

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


prettyTerm
  :: forall a syntax . (Pretty a, RightModule syntax)
  => (forall f sig m . (Carrier sig m, Member (Reader N) sig, Member (Writer (Set.Set N)) sig, Monad f) => (f (m Prec) -> m Prec) -> syntax f (m Prec) -> m Prec)
  -> Term syntax a
  -> Doc
prettyTerm alg = precDoc . snd . run . runWriter @(Set.Set N) . runReader (N 0) . go . fmap (pure . atom . pretty)
  where go :: (Carrier sig m, Member (Reader N) sig, Member (Writer (Set.Set N)) sig) => Term syntax (m Prec) -> m Prec
        go = \case
          Var v -> v
          Term t -> alg go t
