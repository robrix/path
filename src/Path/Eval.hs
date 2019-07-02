{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Eval where

import Path.Core as Core
import Path.Name
import Path.Namespace as Namespace

-- | Evaluate a 'Core' to weak head normal form.
--
--   This involves looking up variables at the head of neutral terms in the environment, but will leave other values alone, as they’re already constructor-headed.
whnf :: Namespace -> Core Qualified -> Core Qualified
whnf scope (n :$ sp) = maybe (n :$ sp) (whnf scope . ($$* sp)) (Namespace.lookup n scope >>= Namespace.entryValue)
whnf _     v         = v
