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
  (==) = (==) `on` quote

instance (Lower v, Ord v) => Ord (Value v) where
  compare = compare `on` quote

instance (Lower v, Show v) => Show (Value v) where
  showsPrec d = showsPrec d . quote

instance (Lower v, Pretty v) => PrettyPrec (Value v) where
  prettyPrec d = prettyPrec d . quote

instance (Lower v, Pretty v) => Pretty (Value v) where
  pretty = prettyPrec 0

vfree :: v -> Value v
vfree = VNeutral . NFree

data Neutral v
  = NFree v
  | NApp (Neutral v) (Value v)

quote :: Lower v => Value v -> Term (Core v) ()
quote VType = In Type ()
quote (VLam v f) = In (Lam v (quote (f (vfree (fromMaybe lowerBound v))))) ()
quote (VPi v e t f) = In (Pi v e (quote t) (quote (f (vfree (fromMaybe lowerBound v))))) ()
quote (VNeutral n) = quoteN n

quoteN :: Lower v => Neutral v -> Term (Core v) ()
quoteN (NFree n) = In (Var n) ()
quoteN (NApp n a) = In (quoteN n :@ quote a) ()
