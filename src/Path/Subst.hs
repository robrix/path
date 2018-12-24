{-# LANGUAGE FunctionalDependencies #-}
module Path.Subst where

import Path.Term

newtype Subst v a = Subst { unSubst :: [(v, a)] }
  deriving (Eq, Ord, Show)


class Eq v => Substitute v f | f -> v where
  subst :: v -> f (Term f a) -> Term f a -> Term f a
