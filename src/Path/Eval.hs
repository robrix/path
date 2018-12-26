{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Eval where

import Control.Effect
import Control.Effect.Reader
import Data.Foldable (foldl')
import Data.Maybe (fromMaybe)
import Path.Back
import Path.Core
import Path.Env as Env
import Path.Name
import Path.Term
import Path.Value

eval :: (Carrier sig m, Functor m, Member (Reader (Env QName)) sig) => Term (Core QName) a -> m (Value QName QName)
eval t = asks (flip go t)
  where go d = \case
          In (Var n) _
            | isLocal n -> fromMaybe (vfree n) (Env.lookup n d)
            | otherwise -> vfree n
          In (Lam n b) _ -> VLam n (flip go b . flip (Env.insert n) d)
          In (f :@ a) _ -> go d f `vapp` go d a
          In Type _ -> VType
          In (Pi n e ty b) _ -> VPi n e (go d ty) (flip go b . flip (Env.insert n) d)

vapp :: Show v => Value v v -> Value v v -> Value v v
vapp (VLam _ f) v = f v
vapp (VNeutral vs n) v = VNeutral (vs :> v) n
vapp f a = error ("illegal application of " <> show f <> " to " <> show a)

vforce :: (Ord v, Show v) => Env v -> Value v v -> Value v v
vforce d = go
  where go = \case
          VLam v f      -> VLam v (go . f)
          VType         -> VType
          VPi v u t b   -> VPi v u (go t) (go . b)
          VNeutral vs n -> foldl' app (maybe (vfree n) go (Env.lookup n d)) vs
        app f a = f `vapp` go a
