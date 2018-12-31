module Path.Unify where

import Control.Effect
import Control.Effect.State
import Path.Core
import Path.Name
import Path.Term
import Text.Trifecta.Rendering (Span)

data Constraint
  = Top
  | Constraint :/\: Constraint
  | Meta :==: Term (Core Name QName) Span
  deriving (Eq, Ord, Show)

runConstraints :: (Carrier sig m, Effect sig, Functor m) => Eff (StateC Constraint m) a -> m a
runConstraints = evalState Top
