{-# LANGUAGE FlexibleContexts, TypeOperators #-}
module Path.Desugar where

import Control.Effect hiding ((:+:))
import Path.Core as Core
import Path.Name
import Path.Surface as Surface
import Path.Term
import Path.Usage

desugar :: (Applicative m, Carrier sig m, Member Fresh sig)
        => Term (Sugar QName :+: Implicit QName :+: Core QName) a
        -> m (Term (Implicit QName :+: Core QName) a)
desugar (In out span) = flip In span <$> case out of
  L (ForAll n t b) -> R <$> (Core.Pi n Zero <$> desugar t <*> desugar b)
  R rest -> traverse desugar rest
