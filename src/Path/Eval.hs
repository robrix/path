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
whnf scope (n :$ sp) = maybe (n :$ sp) (whnf scope . ($$* sp)) (unSpanned . declTerm <$> Module.lookup n scope)
whnf _     v         = v
