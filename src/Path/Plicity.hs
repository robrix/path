module Path.Plicity where

import Path.Semiring

data Plicity = Implicit | Explicit
  deriving (Eq, Ord, Show)

instance Semigroup Plicity where
  Explicit <> _        = Explicit
  _        <> Explicit = Explicit
  _        <> _        = Implicit

instance Monoid Plicity where
  mempty = Implicit

instance Semiring Plicity where
  Implicit >< _        = Implicit
  _        >< Implicit = Implicit
  _        >< _        = Explicit

instance Unital Plicity where
  one = Explicit
