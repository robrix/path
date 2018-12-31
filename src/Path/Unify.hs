module Path.Unify where

import Path.Core
import Path.Name
import Path.Term
import Text.Trifecta.Rendering (Span)

data Constraint
  = Top
  | Constraint :/\: Constraint
  | Meta :==: Term (Core Name QName) Span
  deriving (Eq, Ord, Show)
