{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Eval where

import Data.Void
import Path.Core as Core
import Path.Module as Module
import Path.Name
import Path.Span

-- | Evaluate a 'Core' to weak head normal form.
--
--   This involves looking up variables at the head of neutral terms in the environment, but will leave other values alone, as they’re already constructor-headed.
whnf :: ModuleGraph Core Void -> Core Qualified -> Core Qualified
whnf graph = go where
  go (n :$ sp) = maybe (n :$ sp) (go . ($$* sp)) (unSpanned . declTerm <$> Module.lookup n graph)
  go v         = v
