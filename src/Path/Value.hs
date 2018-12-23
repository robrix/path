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
  = VLam v (Value v -> Value v)
  | VType
  | VPi v Usage (Value v) (Value v -> Value v)
  | VNeutral [Value v] v                       -- ^ A neutral term defined as a list of applications in reverse (i.e. &, not $) order.

instance Eq v => Eq (Value v) where
  (==) = aeq

instance Ord v => Ord (Value v) where
  compare = compare `on` quote const

instance Show v => Show (Value v) where
  showsPrec d = showsPrec d . quote (flip const)

instance (Ord v, Pretty v) => PrettyPrec (Value v) where
  prettyPrec d = prettyPrec d . quote (flip const)

instance (Ord v, Pretty v) => Pretty (Value v) where
  pretty = prettyPrec 0

instance Ord v => FreeVariables v (Value v) where
  fvs = fvs . quote (flip const)

vfree :: v -> Value v
vfree = VNeutral []


quote :: (Int -> v -> u) -> Value v -> Term (Core u) ()
quote f = go 0
  where go i = \case
          VType -> In Type ()
          VLam n b -> In (Lam (f i n) (go (succ i) (b (vfree n)))) ()
          VPi n e t b -> In (Pi (f i n) e (go i t) (go (succ i) (b (vfree n)))) ()
          VNeutral as n -> foldr (fmap (flip In ()) . (:@) . go i) (In (Var (f i n)) ()) as

aeq :: Eq v => Value v -> Value v -> Bool
aeq = go (0 :: Int) [] []
  where go i env1 env2 v1 v2 = case (v1, v2) of
          (VType,           VType)           -> True
          (VLam n1 b1,      VLam n2 b2)      -> go (succ i) ((n1, i) : env1) ((n2, i) : env2) (b1 (vfree n1)) (b2 (vfree n2))
          (VPi n1 e1 t1 b1, VPi n2 e2 t2 b2) -> e1 == e2 && go i env1 env2 t1 t2 && go (succ i) ((n1, i) : env1) ((n2, i) : env2) (b1 (vfree n1)) (b2 (vfree n2))
          (VNeutral as1 n1, VNeutral as2 n2) -> fromMaybe (n1 == n2) ((==) <$> lookup n1 env1 <*> lookup n2 env2) && length as1 == length as2 && and (zipWith (go i env1 env2) as1 as2)
          _                                  -> False
