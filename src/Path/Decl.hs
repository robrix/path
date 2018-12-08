module Path.Decl where

import Path.Usage

data Decl a
  = Declare String a
  | Define String Usage a
  deriving (Eq, Ord, Show)
