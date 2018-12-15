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

vapp :: Value QName -> Value QName -> Value QName
vapp (VLam _ f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)
vapp f a = error ("illegal application of " <> show f <> " to " <> show a)

vforce :: Value QName -> Env QName -> Value QName
vforce (VLam v f) d = VLam v (flip vforce d . f)
vforce VType _ = VType
vforce (VPi v u t b) d = VPi v u (vforce t d) (flip vforce d . b)
vforce (VNeutral n) d = vforceN n d

vforceN :: Neutral QName -> Env QName -> Value QName
vforceN (NApp f a) d = vforceN f d `vapp` vforce a d
vforceN (NFree v) d = maybe (vfree v) (flip vforce d) (Env.lookup v d)
