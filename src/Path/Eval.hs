module Path.Eval where

import Data.Function (on)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Path.Core
import Path.FreeVariables
import Path.Name
import Path.Pretty
import Path.Term
import Path.Usage
import Text.PrettyPrint.ANSI.Leijen

data Value
  = VLam String (Value -> Value)
  | VType
  | VPi String Usage Value (Value -> Value)
  | VNeutral Neutral

instance Eq Value where
  (==) = (==) `on` quote

instance Ord Value where
  compare = compare `on` quote

instance Show Value where
  showsPrec d = showsPrec d . quote

instance PrettyPrec Value where
  prettyPrec d = prettyPrec d . quote

instance Pretty Value where
  pretty = prettyPrec 0

instance FreeVariables Value where
  fvs = fvs . quote

vfree :: Name -> Value
vfree = VNeutral . NFree

data Neutral
  = NFree Name
  | NApp Neutral Value
  deriving (Eq, Ord, Show)

quote :: Value -> Term Core
quote VType = In Type
quote (VLam v f) = In (Lam v (quote (f (vfree (Quote v)))))
quote (VPi v e t f) = In (Pi v e (quote t) (quote (f (vfree (Quote v)))))
quote (VNeutral n) = quoteN n

quoteN :: Neutral -> Term Core
quoteN (NFree (Quote s)) = In (Var (Local s))
quoteN (NFree n) = In (Var n)
quoteN (NApp n a) = In (quoteN n :@ quote a)


type Env = Map.Map String Value

eval :: Term Core -> Env -> Value
eval (In (Var (Local n))) d = fromMaybe (vfree (Local n)) (Map.lookup n d)
eval (In (Var (Global n))) d = fromMaybe (vfree (Global n)) (Map.lookup n d)
eval (In (Var (Quote n))) d = fromMaybe (vfree (Quote n)) (Map.lookup n d)
eval (In (Lam n b)) d = VLam n (eval b . flip (Map.insert n) d)
eval (In (f :@ a)) d = eval f d `vapp` eval a d
eval (In Type) _ = VType
eval (In (Pi n e ty body)) d = VPi n e (eval ty d) (eval body . flip (Map.insert n) d)

vapp :: Value -> Value -> Value
vapp (VLam _ f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)
vapp f a = error ("illegal application of " <> show f <> " to " <> show a)
