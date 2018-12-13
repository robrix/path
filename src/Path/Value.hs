module Path.Value where

import Data.Function (on)
import Data.Maybe (fromMaybe)
import Data.Semilattice.Lower
import Path.Core
import Path.Pretty
import Path.Term
import Path.Usage
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

data Value v
  = VLam (Maybe v) (Value v -> Value v)
  | VType
  | VPi (Maybe v) Usage (Value v) (Value v -> Value v)
  | VNeutral (Neutral v)

instance (Eq v, Lower v) => Eq (Value v) where
  (==) = (==) `on` quote lowerBound

instance (Lower v, Ord v) => Ord (Value v) where
  compare = compare `on` quote lowerBound

instance (Lower v, Show v) => Show (Value v) where
  showsPrec d = showsPrec d . quote lowerBound

instance (Lower v, Pretty v) => PrettyPrec (Value v) where
  prettyPrec d = prettyPrec d . quote lowerBound

instance (Lower v, Pretty v) => Pretty (Value v) where
  pretty = prettyPrec 0

vfree :: v -> Value v
vfree = VNeutral . NFree

data Neutral v
  = NFree v
  | NApp (Neutral v) (Value v)

quote :: v -> Value v -> Term (Core v) ()
quote _ VType = In Type ()
quote v (VLam n f) = In (Lam n (quote v (f (vfree (fromMaybe v n))))) ()
quote v (VPi n e t f) = In (Pi n e (quote v t) (quote v (f (vfree (fromMaybe v n))))) ()
quote v (VNeutral n) = quoteN v n

quoteN :: v -> Neutral v -> Term (Core v) ()
quoteN _ (NFree n) = In (Var n) ()
quoteN v (NApp n a) = In (quoteN v n :@ quote v a) ()
