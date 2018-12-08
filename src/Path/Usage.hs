module Path.Usage where

data Usage
  = Zero
  | One
  | More
  deriving (Eq, Ord, Show)
