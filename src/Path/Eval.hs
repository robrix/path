module Path.Eval where

import Data.Function (on)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Path.Core
import Path.FreeVariables
import Path.Name
import Path.Plicity
import Path.Pretty
import Path.Term

data Value
  = VLam String (Value -> Value)
  | VType
  | VPi String Plicity Value (Value -> Value)
  | VNeutral Neutral

instance Eq Value where
  (==) = (==) `on` quote

instance Ord Value where
  compare = compare `on` quote

instance Show Value where
  showsPrec d = showsPrec d . quote

instance PrettyPrec Value where
  prettyPrec d = prettyPrec d . quote

instance FreeVariables Value where
  fvs = fvs . quote

vfree :: Name -> Value
vfree = VNeutral . NFree

data Neutral
  = NFree Name
  | NApp Neutral Value
  deriving (Eq, Ord, Show)

quote :: Value -> Term Core ()
quote VType = Term Type
quote (VLam v f) = Term (Lam v (quote (f (vfree (Quote v)))))
quote (VPi v e t f) = Term (Pi v e (quote t) (quote (f (vfree (Quote v)))))
quote (VNeutral n) = quoteN n

quoteN :: Neutral -> Term Core ()
quoteN (NFree (Quote s)) = Term (Bound s)
quoteN (NFree n) = Term (Free n)
quoteN (NApp n a) = Term (quoteN n :@ quote a)


type Env = Map.Map String Value

eval :: Term Core a -> Env -> Value
eval (Term (Bound i)) d = d Map.! i
eval (Term (Free (Local n))) d = fromMaybe (vfree (Local n)) (Map.lookup n d)
eval (Term (Free (Global n))) d = fromMaybe (vfree (Global n)) (Map.lookup n d)
eval (Term (Free (Quote n))) d = fromMaybe (vfree (Quote n)) (Map.lookup n d)
eval (Term (Lam n b)) d = VLam n (eval b . flip (Map.insert n) d)
eval (Term (f :@ a)) d = eval f d `vapp` eval a d
eval (Term Type) _ = VType
eval (Term (Pi n e ty body)) d = VPi n e (eval ty d) (eval body . flip (Map.insert n) d)

vapp :: Value -> Value -> Value
vapp (VLam _ f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)
