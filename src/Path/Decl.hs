module Path.Decl where

data Decl a
  = Declare String a
  | Define String a
  deriving (Eq, Ord, Show)
