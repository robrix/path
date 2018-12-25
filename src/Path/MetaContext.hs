module Path.MetaContext where

data Equation tm ty = (tm, ty) :==: (tm, ty)
  deriving (Eq, Ord, Show)
