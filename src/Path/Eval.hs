module Path.Eval where

import qualified Data.Map as Map
import Path.Expr

type Env = Map.Map String Value

eval :: Term Core -> Env -> Value
eval (Term (Bound i)) d = d Map.! i
eval (Term (Free name)) _ = vfree name
eval (Term (Lam n b)) d = VLam (eval b . flip (Map.insert n) d)
eval (Term (f :@ a)) d = eval f d `vapp` eval a d
eval (Term Type) _ = VType
eval (Term (Pi n ty body)) d = VPi (eval ty d) (eval body . flip (Map.insert n) d)

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)
