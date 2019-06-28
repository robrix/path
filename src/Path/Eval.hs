{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Eval where

import Path.Name
import Path.Scope as Scope
import Path.Value as Value

-- | Evaluate a 'Value' to weak head normal form.
--
--   This involves looking up variables at the head of neutral terms in the environment, but will leave other values alone, as they’re already constructor-headed.
whnf :: Scope -> Value Gensym -> Value Gensym
whnf scope (Value (Global n :$ sp)) = maybe (Value (Global n :$ sp)) (whnf scope . ($$* sp)) (Scope.lookup n scope >>= Scope.entryValue)
whnf _     v                        = v
