{-# LANGUAGE DeriveTraversable #-}
module Path.Plicity where

import Path.Pretty
import Path.Semiring

data Plicity = Im | Ex
  deriving (Eq, Ord, Show)

plicity :: (Eq a, Monoid a) => a -> Plicity
plicity a | a == zero = zero
          | otherwise = one

instance Semigroup Plicity where
  Ex <> _  = Ex
  _  <> Ex = Ex
  _  <> _  = Im

instance Monoid Plicity where
  mempty = Im

instance Semiring Plicity where
  Im >< _  = Im
  _  >< Im = Im
  _  >< _  = Ex

instance Unital Plicity where
  one = Ex


prettyPlicity :: Bool -> Plicit Doc -> Doc
prettyPlicity _    (Im :< a) = prettyBraces True a
prettyPlicity True (Ex :< a) = prettyParens True a
prettyPlicity _    (_  :< a) = a


data Plicit a
  = Plicity :< a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 7 :<

instance Pretty a => Pretty (Plicit a) where
  pretty = prettyPlicity True . fmap pretty
