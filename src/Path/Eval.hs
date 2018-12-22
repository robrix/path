{-# LANGUAGE LambdaCase #-}
module Path.Eval where

import Data.Maybe (fromMaybe)
import Path.Core
import Path.Env as Env
import Path.Name
import Path.Term
import Path.Value

eval :: Env QName -> Term (Core QName) a -> Value QName
eval d = \case
  In (Var n) _
    | isLocal n -> fromMaybe (vfree n) (Env.lookup n d)
    | otherwise -> vfree n
  In (Lam n b) _ -> VLam n (flip eval b . flip (Env.insert n) d)
  In (f :@ a) _ -> eval d f `vapp` eval d a
  In Type _ -> VType
  In (Pi n e ty b) _ -> VPi n e (eval d ty) (flip eval b . flip (Env.insert n) d)

vapp :: Show v => Value v -> Value v -> Value v
vapp (VLam _ f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)
vapp f a = error ("illegal application of " <> show f <> " to " <> show a)

vforce :: (Ord v, Show v) => Env v -> Value v -> Value v
vforce d = go
  where go = \case
          VLam v f    -> VLam v (go . f)
          VType       -> VType
          VPi v u t b -> VPi v u (go t) (go . b)
          VNeutral n  -> goN n
        goN = \case
          NApp f a -> goN f `vapp` go a
          NFree v  -> maybe (vfree v) go (Env.lookup v d)
