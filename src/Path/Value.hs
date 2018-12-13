module Path.Value where

import Data.Function (on)
import Data.Maybe (fromMaybe)
import Path.Core
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
