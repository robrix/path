{-# LANGUAGE TypeOperators #-}
module Path.Constraint where

import Path.Context
import Path.Core
import Path.Name
import Path.Term
import Text.Trifecta.Rendering (Span)

data Constraint = Constraint
  { constraintContext :: Context
  , constraintLhs     :: Term (Implicit QName :+: Core Name QName) Span
  , constraintRhs     :: Term (Implicit QName :+: Core Name QName) Span
  , constraintType    :: Type QName
  }
