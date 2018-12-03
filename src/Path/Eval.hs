module Path.Eval where

import Data.Function (on)
import qualified Data.Map as Map
import Path.Expr

data Value
  = VLam (Value -> Value)
  | VType
  | VPi Value (Value -> Value)
  | VNeutral Neutral

instance Eq Value where
  (==) = (==) `on` quote 0

instance Ord Value where
  compare = compare `on` quote 0

instance Show Value where
  showsPrec d = showsPrec d . quote 0

vfree :: Name -> Value
vfree = VNeutral . NFree

data Neutral
  = NFree Name
  | NApp Neutral Value
  deriving (Eq, Ord, Show)

prettyVar :: Int -> String
prettyVar d = let (n, i) = d `divMod` 26 in replicate (succ n) (alphabet !! i)
  where alphabet = ['a'..'z']

quote :: Int -> Value -> Term Core
quote _ VType = Term Type
quote i (VLam f) = let v = prettyVar i in Term (Lam v (quote (succ i) (f (vfree (Quote v)))))
quote i (VPi t f) = let v = prettyVar i in Term (Pi v (quote i t) (quote (succ i) (f (vfree (Quote v)))))
quote i (VNeutral n) = quoteN i n

quoteN :: Int -> Neutral -> Term Core
quoteN _ (NFree (Quote s)) = Term (Bound s)
quoteN _ (NFree n) = Term (Free n)
quoteN i (NApp n a) = Term (quoteN i n :@ quote i a)


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
