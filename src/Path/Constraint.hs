{-# LANGUAGE TypeOperators #-}
module Path.Constraint where

import Path.Context
import Path.Core
import Path.Name
import Path.Term
import Text.Trifecta.Rendering (Span)

data Equation = Term (Implicit QName :+: Core Name QName) Span :==: Term (Implicit QName :+: Core Name QName) Span

data Constraint = Equation ::: Type QName
