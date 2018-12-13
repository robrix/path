{-# LANGUAGE FlexibleInstances, LambdaCase, MultiParamTypeClasses #-}
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

instance Ord v => Eq (Value v) where
  (==) = aeq `on` quote (flip const)

instance Ord v => Ord (Value v) where
  compare = compare `on` quote (flip const)

instance Show v => Show (Value v) where
  showsPrec d = showsPrec d . quote (flip const)

instance (Ord v, Pretty v) => PrettyPrec (Value v) where
  prettyPrec d = prettyPrec d . quote (flip const)

instance (Ord v, Pretty v) => Pretty (Value v) where
  pretty = prettyPrec 0

instance Ord v => FreeVariables v (Value v) where
  fvs = fvs . quote (flip const)

vfree :: v -> Value v
vfree = VNeutral . NFree

data Neutral v
  = NFree v
  | NApp (Neutral v) (Value v)

quote :: (Int -> v -> u) -> Value v -> Term (Core u) ()
quote f = go 0
  where go i = \case
          VType -> In Type ()
          VLam n b -> In (Lam (f i <$> n) (go (succ i) (b (vfree (fromMaybe undefined n))))) ()
          VPi n e t b -> In (Pi (f i <$> n) e (go i t) (go (succ i) (b (vfree (fromMaybe undefined n))))) ()
          VNeutral n -> goN i n

        goN i (NFree n) = In (Var (f i n)) ()
        goN i (NApp n a) = In (goN i n :@ go i a) ()
