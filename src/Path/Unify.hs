{-# LANGUAGE DeriveTraversable #-}
module Path.Unify where

data Back a = Nil | Back a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Twin = Only | TwinL | TwinR
  deriving (Eq, Ord, Show)

data Equation tm ty = (tm, ty) :==: (tm, ty)
  deriving (Eq, Ord, Show)

sym :: Equation tm ty -> Equation tm ty
sym (s :==: t) = t :==: s
