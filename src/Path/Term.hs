{-# LANGUAGE DeriveTraversable, FlexibleInstances, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, RankNTypes, ScopedTypeVariables, StandaloneDeriving, UndecidableInstances #-}
module Path.Term where

import Path.Fin
import Path.Pretty
import Path.Vec
import Syntax.Module
import Syntax.Term
import Syntax.Var

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
prettyTermInContext alg = go where
  go :: forall n . Vec n Doc -> Term sig (Var (Fin n) a) -> Prec
  go ctx = \case
    Var v -> atom (unVar (ctx !) pretty v)
    Alg t -> alg go ctx t
