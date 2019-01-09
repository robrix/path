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

eval :: Env -> Term (Core (Typed Name) (Typed QName)) a -> Value
eval env = \case
  In (Core.Free (Local n ::: t)) _ -> fromMaybe (free (Local n ::: t)) (Env.lookup n env)
  In (Core.Free v) _ -> free v
  In (Core.Lam (n ::: t) b) _ -> Value.Lam t (\ v -> eval (Env.insert n v env) b)
  In (f Core.:$ a) _ -> eval env f $$ eval env a
  In Core.Type _ -> Value.Type
  In (Core.Pi (n ::: _) p u t b) _ -> Value.Pi p u (eval env t) (\ v -> eval (Env.insert n v env) b)

-- | Evaluate a 'Value' to weak head normal form.
--
--   This involves looking up variables at the head of neutral terms in the environment, but will leave other values alone, as they’re already constructor-headed.
whnf :: (Carrier sig m, Member (Reader Scope) sig, Monad m) => Value -> m Value
whnf ((Value.Free (m :.: n) ::: t) Value.:$ sp) = asks (entryValue <=< Scope.lookup (m :.: n)) >>= maybe (pure ((Value.Free (m :.: n) ::: t) Value.:$ sp)) (whnf . ($$* sp))
whnf v                                          = pure v
