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
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

data Value
  = VLam (Maybe String) (Value -> Value)
  | VType
  | VPi (Maybe String) Usage Value (Value -> Value)
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

quote :: Value -> Term (Core Name) ()
quote VType = In Type ()
quote (VLam v f) = In (Lam (Name <$> v) (quote (f (vfree (Name (fromMaybe "_" v)))))) ()
quote (VPi v e t f) = In (Pi (Name <$> v) e (quote t) (quote (f (vfree (Name (fromMaybe "_" v)))))) ()
quote (VNeutral n) = quoteN n

quoteN :: Neutral -> Term (Core Name) ()
quoteN (NFree n) = In (Var n) ()
quoteN (NApp n a) = In (quoteN n :@ quote a) ()


type Env = Map.Map String Value

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
