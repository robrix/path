{-# LANGUAGE TypeOperators #-}
module Path.Desugar where

import Path.Core as Core
import Path.Name
import Path.Surface as Surface
import Path.Term
import Path.Usage

desugar :: Term (Sugar QName :+: Implicit QName :+: Core QName) a
        -> Term (Implicit QName :+: Core QName) a
desugar (In out span) = flip In span $ case out of
  L (ForAll' n t b) -> R (Core.Pi n Zero (desugar t) (desugar b))
  R rest -> desugar <$> rest
