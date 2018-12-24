{-# LANGUAGE DeriveTraversable #-}
module Path.Unify where

import Path.Name

data Back a = Nil | Back a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Twin = Only | TwinL | TwinR
  deriving (Eq, Ord, Show)

data Equation tm ty = (tm, ty) :==: (tm, ty)
  deriving (Eq, Ord, Show)

sym :: Equation tm ty -> Equation tm ty
sym (s :==: t) = t :==: s

data Param ty = P ty | ty :++: ty
  deriving (Eq, Ord, Show)

data Dec a = Hole | Defn a
  deriving (Eq, Ord, Show)

data Entry tm ty
  = E QName ty (Dec tm)
  | Q Status (Problem tm ty)
  deriving (Eq, Ord, Show)

data Status = Blocked | Active
  deriving (Eq, Ord, Show)

data Problem tm ty
  = Unify (Equation tm ty)
  | All (Param ty) QName (Problem tm ty)
  deriving (Eq, Ord, Show)
