module Path.Decl where

data Decl v a
  = Declare v a
  | Define v a
  deriving (Eq, Ord, Show)
