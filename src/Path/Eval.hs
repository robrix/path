{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Eval where

import Control.Effect
import Control.Effect.Reader
import Data.Foldable (foldl')
import Data.Maybe (fromMaybe)
import Path.Back
import Path.Core as Core
import Path.Env as Env
import Path.Name
import Path.Term
import Path.Value as Value

eval :: (Carrier sig m, Functor m, Member (Reader (Env QName)) sig) => Term (Core QName) a -> m (Value QName)
eval t = asks (flip go t)
  where go d = \case
          In (Core.Var n) _
            | isLocal n -> fromMaybe (vfree n) (Env.lookup n d)
            | otherwise -> vfree n
          In (Core.Lam n b) _ -> Value.Lam n (flip go b . flip (Env.insert n) d)
          In (f :@ a) _ -> go d f `vapp` go d a
          In Core.Type _ -> Value.Type
          In (Core.Pi n e ty b) _ -> Value.Pi n e (go d ty) (flip go b . flip (Env.insert n) d)

vapp :: Show v => Value v -> Value v -> Value v
vapp (Value.Lam _ f) v = f v
vapp (Value.Neutral vs n) v = Value.Neutral (vs :> v) n
vapp f a = error ("illegal application of " <> show f <> " to " <> show a)

vforce :: (Ord v, Show v) => Env v -> Value v -> Value v
vforce d = go
  where go = \case
          Value.Lam v f      -> Value.Lam v (go . f)
          Value.Type         -> Value.Type
          Value.Pi v u t b   -> Value.Pi v u (go t) (go . b)
          Value.Neutral vs n -> foldl' app (maybe (vfree n) go (Env.lookup n d)) vs
        app f a = f `vapp` go a
