module Path.Name where

data Name
  = Global String
  | Local String
  | Quote String
  deriving (Eq, Ord, Show)
