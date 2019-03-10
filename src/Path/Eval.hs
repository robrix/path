{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Eval where

import Control.Effect
import Control.Effect.Reader hiding (Reader(Local))
import Control.Monad ((<=<))
import Path.Name
import Path.Scope as Scope
import Path.Value as Value hiding (Scope(..))

-- | Evaluate a 'Value' to weak head normal form.
--
--   This involves looking up variables at the head of neutral terms in the environment, but will leave other values alone, as they’re already constructor-headed.
whnf :: (Carrier sig m, Member (Reader Scope) sig) => Value MName -> m (Value MName)
whnf (Q (m :.: n) Value.:$ sp) = asks (entryValue <=< Scope.lookup (m :.: n)) >>= maybe (pure (Q (m :.: n) Value.:$ sp)) (whnf . ($$* sp))
whnf v                         = pure v
