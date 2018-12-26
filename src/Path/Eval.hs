{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Eval where

import Control.Effect
import Control.Effect.Reader hiding (Reader(Local))
import Data.Foldable (foldl')
import Data.Maybe (fromMaybe)
import Path.Core as Core
import Path.Env as Env
import Path.Name
import Path.Term
import Path.Value as Value

eval :: (Carrier sig m, Functor m, Member (Reader Env) sig) => Term Core a -> m Value
eval t = asks (flip go t)
  where go d = \case
          In (Core.Var n) _
            | isLocal n -> fromMaybe (vfree n) (Env.lookup n d)
            | otherwise -> vfree n
          In (Core.Lam n b) _ -> Value.Lam n (go (Env.insert (Local n) (vfree (Local n)) d) b)
          In (f :@ a) _ -> go d f `vapp` go d a
          In Core.Type _ -> Value.Type
          In (Core.Pi n e ty b) _ -> Value.Pi n e (go d ty) (go (Env.insert (Local n) (vfree (Local n)) d) b)

vforce :: Env -> Value -> Value
vforce d = go
  where go = \case
          Value.Lam v b      -> Value.Lam v (go b)
          Value.Type         -> Value.Type
          Value.Pi v u t b   -> Value.Pi v u (go t) (go b)
          Value.Neutral vs n -> foldl' app (maybe (vfree n) go (Env.lookup n d)) vs
        app f a = f `vapp` go a
