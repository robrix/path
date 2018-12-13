{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module Path.Value where

import Data.Function (on)
import Data.Maybe (fromMaybe)
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

instance Eq v => Eq (Value v) where
  (==) = (==) `on` quote

instance Ord v => Ord (Value v) where
  compare = compare `on` quote

instance Show v => Show (Value v) where
  showsPrec d = showsPrec d . quote

instance (Ord v, Pretty v) => PrettyPrec (Value v) where
  prettyPrec d = prettyPrec d . quote

instance (Ord v, Pretty v) => Pretty (Value v) where
  pretty = prettyPrec 0

instance Ord v => FreeVariables v (Value v) where
  fvs = fvs . quote

vfree :: v -> Value v
vfree = VNeutral . NFree

data Neutral v
  = NFree v
  | NApp (Neutral v) (Value v)

quote :: Value v -> Term (Core v) ()
quote VType = In Type ()
quote (VLam n f) = In (Lam n (quote (f (vfree (fromMaybe undefined n))))) ()
quote (VPi n e t f) = In (Pi n e (quote t) (quote (f (vfree (fromMaybe undefined n))))) ()
quote (VNeutral n) = quoteN n

quoteN :: Neutral v -> Term (Core v) ()
quoteN (NFree n) = In (Var n) ()
quoteN (NApp n a) = In (quoteN n :@ quote a) ()
