{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Eval where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader hiding (Reader(Local))
import Data.Maybe (fromMaybe)
import Path.Core as Core
import Path.Context
import Path.Env as Env
import Path.Error
import Path.Name
import Path.Term
import Path.Value as Value
import Text.Trifecta.Rendering (Span)

eval :: (Carrier sig m, Functor m, Member (Reader Env) sig) => Term (Core Name QName) a -> m Value
eval tm = asks (flip go tm)
  where go env = \case
          In (Core.Var n) _
            | isLocal n -> fromMaybe (vfree n) (Env.lookup n env)
            | otherwise -> vfree n
          In (Core.Lam n b) _ -> Value.Lam (\ v -> go (Env.insert (Local n) v env) b)
          In (f :$ a) _ -> go env f $$ go env a
          In Core.Type _ -> Value.Type
          In (Core.Pi n p u t b) _ -> Value.Pi p u (go env t) (\ v -> go (Env.insert (Local n) v env) b)

vforce :: (Carrier sig m, Functor m, Member (Reader Env) sig) => Value -> m Value
vforce v = asks (flip go v)
  where go env = \case
          Value.Lam b      -> Value.Lam (go env . b)
          Value.Type       -> Value.Type
          Value.Pi p u t b -> Value.Pi p u (go env t) (go env . b)
          vs :& n          -> maybe (vfree n) (go env) (Env.lookup n env) $$* (go env <$> vs)

lookupDef :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader Env) sig, Member (Reader Span) sig, Monad m) => QName -> m Type
lookupDef n = asks (Env.lookup n) >>= maybe (FreeVariable n <$> ask >>= throwError) pure

whnf :: (Carrier sig m, Member (Error ElabError) sig, Member (Reader Env) sig, Member (Reader Span) sig, Monad m) => Value -> m Value
whnf (sp :& n) = ($$* sp) <$> lookupDef n
whnf v         = pure v
