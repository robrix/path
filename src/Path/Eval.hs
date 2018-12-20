{-# LANGUAGE LambdaCase #-}
module Path.Eval where

import Data.Maybe (fromMaybe)
import Path.Core
import Path.Env as Env
import Path.Name
import Path.Term
import Path.Value

eval :: Term (Core QName) a -> Env QName -> Value QName
eval (In (Var n) _) d
  | isLocal n = fromMaybe (vfree n) (Env.lookup n d)
  | otherwise = vfree n
eval (In (Lam n b) _) d = VLam n (eval b . flip (Env.insert n) d)
eval (In (f :@ a) _) d = eval f d `vapp` eval a d
eval (In Type _) _ = VType
eval (In (Pi n e ty b) _) d = VPi n e (eval ty d) (eval b . flip (Env.insert n) d)

vapp :: Show v => Value v -> Value v -> Value v
vapp (VLam _ f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)
vapp f a = error ("illegal application of " <> show f <> " to " <> show a)

vforce :: (Ord v, Show v) => Env v -> Value v -> Value v
vforce d = \case
  VLam v f    -> VLam v (vforce d . f)
  VType       -> VType
  VPi v u t b -> VPi v u (vforce d t) (vforce d . b)
  VNeutral n  -> vforceN d n

vforceN :: (Ord v, Show v) => Env v -> Neutral v -> Value v
vforceN d = \case
  NApp f a -> vforceN d f `vapp` vforce d a
  NFree v  -> maybe (vfree v) (vforce d) (Env.lookup v d)
