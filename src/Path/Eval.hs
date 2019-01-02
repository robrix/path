{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Eval where

import Control.Effect
import Control.Effect.Reader hiding (Reader(Local))
import Control.Monad ((<=<))
import Data.Maybe (fromMaybe)
import Path.Core as Core
import Path.Env as Env
import Path.Name
import Path.Scope as Scope
import Path.Term
import Path.Value as Value

eval :: (Carrier sig m, Functor m, Member (Reader Env) sig) => Term (Core Name QName) a -> m Value
eval tm = asks (flip go tm)
  where go env = \case
          In (Core.Var (Local n)) _ -> fromMaybe (vfree (Local n)) (Env.lookup n env)
          In (Core.Var (m :.: n)) _ -> vfree (m :.: n)
          In (Core.Lam n b) _ -> Value.Lam (\ v -> go (Env.insert n v env) b)
          In (f :$ a) _ -> go env f $$ go env a
          In Core.Type _ -> Value.Type
          In (Core.Pi n p u t b) _ -> Value.Pi p u (go env t) (\ v -> go (Env.insert n v env) b)

-- | Evaluate a 'Value' to weak head normal form.
--
--   This involves looking up variables at the head of neutral terms in the environment, but will leave other values alone, as they’re already constructor-headed.
whnf :: (Carrier sig m, Member (Reader Env) sig, Member (Reader Scope) sig, Monad m) => Value -> m Value
whnf (sp :& (m :.: n)) = asks (entryValue <=< Scope.lookup (m :.: n)) >>= maybe (pure (sp :& (m :.: n))) (whnf . ($$* sp))
whnf (sp :& (Local n)) = asks (Env.lookup n) >>= maybe (pure (sp :& Local n)) (whnf . ($$* sp))
whnf v                 = pure v
