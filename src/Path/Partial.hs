module Path.Partial where

import Path.Name
import Path.Plicity
import Path.Stack
import Path.Usage

data Partial
  = Type
  | Lam Scope
  | Pi Plicity Usage Partial Scope
  | Head :$ Stack Partial
  deriving (Eq, Ord, Show)

newtype Scope = Scope Partial
  deriving (Eq, Ord, Show)
