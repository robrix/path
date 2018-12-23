module Path.Unify where

data Twin = Only | TwinL | TwinR
  deriving (Eq, Ord, Show)

newtype Subst v a = Subst { unSubst :: [(v, a)] }
  deriving (Eq, Ord, Show)
