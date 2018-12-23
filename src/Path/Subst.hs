module Path.Subst where

newtype Subst v a = Subst { unSubst :: [(v, a)] }
  deriving (Eq, Ord, Show)
