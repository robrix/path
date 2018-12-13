module Path.Eval where

import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Path.Core
import Path.Env
import Path.Name
import Path.Term
import Path.Value

eval :: Term (Core Name) a -> Env -> Value
eval (In (Var n) _) d = fromMaybe (vfree n) (Map.lookup (getName n) d)
eval (In (Lam n b) _) d = VLam (getName <$> n) (eval b . maybe const (flip . Map.insert . getName) n d)
eval (In (f :@ a) _) d = eval f d `vapp` eval a d
eval (In Type _) _ = VType
eval (In (Pi n e ty b) _) d = VPi (getName <$> n) e (eval ty d) (eval b . maybe const (flip . Map.insert . getName) n d)

vapp :: Value -> Value -> Value
vapp (VLam _ f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)
vapp f a = error ("illegal application of " <> show f <> " to " <> show a)
