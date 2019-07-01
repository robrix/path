{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Eval where

import Path.Name
import Path.Namespace as Namespace
import Path.Value as Value

-- | Evaluate a 'Value' to weak head normal form.
--
--   This involves looking up variables at the head of neutral terms in the environment, but will leave other values alone, as they’re already constructor-headed.
whnf :: Namespace -> Value (Name Gensym) -> Value (Name Gensym)
whnf scope (Value (Global n :$ sp)) = maybe (Value (Global n :$ sp)) (whnf scope . ($$* sp)) (Namespace.lookup n scope >>= Namespace.entryValue)
whnf _     v                        = v
