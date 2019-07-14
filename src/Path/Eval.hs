{-# LANGUAGE FlexibleContexts, LambdaCase, TypeOperators #-}
module Path.Eval where

import Control.Effect.Sum
import Data.Void
import Path.Module as Module
import Path.Name
import Path.Problem
import Path.Span
import Path.Term

-- | Evaluate a term to weak head normal form.
--
--   This involves looking up variables at the head of neutral terms in the environment, but will leave other values alone, as they’re already constructor-headed.
whnf :: ModuleGraph (Term (Problem :+: Core)) Void -> Term (Problem :+: Core) Qualified -> Term (Problem :+: Core) Qualified
whnf graph = go where
  go (Term (R (Var n :$ a))) = maybe (Var n $$ a) (go . ($$ a) . unSpanned . declTerm) (Module.lookup n graph)
  go v                       = v
