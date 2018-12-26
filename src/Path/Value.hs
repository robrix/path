{-# LANGUAGE FlexibleInstances, LambdaCase, MultiParamTypeClasses #-}
module Path.Value where

import Data.Foldable (foldl')
import Data.Function (on)
import Data.Maybe (fromMaybe)
import Path.Back as Back
import Path.Core
import Path.Pretty
import Path.Term
import Path.Usage
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

data Value m v
  = VType                                                 -- ^ @'Type' : 'Type'@.
  | VLam v                   (Value m v -> m (Value m v)) -- ^ A HOAS-encoded lambda abstraction.
  | VPi  v Usage (Value m v) (Value m v -> m (Value m v)) -- ^ A HOAS-encoded ∏ type, with a 'Usage' annotation.
  | VNeutral (Back (Value m v)) v                         -- ^ A neutral term represented as a function on the right and a list of arguments to apply it to in reverse (i.e. &, not $) order.

newtype I a = I { unI :: a }

instance Eq v => Eq (Value I v) where
  (==) = aeq

instance Ord v => Ord (Value I v) where
  compare = compare `on` quote const

instance Show v => Show (Value I v) where
  showsPrec d = showsPrec d . quote (flip const)

instance (Ord v, Pretty v) => PrettyPrec (Value I v) where
  prettyPrec d = prettyPrec d . quote (flip const)

instance (Ord v, Pretty v) => Pretty (Value I v) where
  pretty = prettyPrec 0

instance Ord v => FreeVariables v (Value I v) where
  fvs = fvs . quote (flip const)

vfree :: v -> Value m v
vfree = VNeutral Nil


quote :: (Int -> v -> u) -> Value I v -> Term (Core u) ()
quote f = go 0
  where go i = \case
          VType         -> In Type ()
          VLam n b      -> In (Lam (f i n) (go (succ i) (unI (b (vfree n))))) ()
          VPi n e t b   -> In (Pi (f i n) e (go i t) (go (succ i) (unI (b (vfree n))))) ()
          VNeutral as n -> foldl' app (In (Var (f i n)) ()) as
          where app f a = In (f :@ go i a) ()

aeq :: Eq v => Value I v -> Value I v -> Bool
aeq = go (0 :: Int) [] []
  where go i env1 env2 v1 v2 = case (v1, v2) of
          (VType,           VType)           -> True
          (VLam n1 b1,      VLam n2 b2)      -> go (succ i) ((n1, i) : env1) ((n2, i) : env2) (unI (b1 (vfree n1))) (unI (b2 (vfree n2)))
          (VPi n1 e1 t1 b1, VPi n2 e2 t2 b2) -> e1 == e2 && go i env1 env2 t1 t2 && go (succ i) ((n1, i) : env1) ((n2, i) : env2) (unI (b1 (vfree n1))) (unI (b2 (vfree n2)))
          (VNeutral as1 n1, VNeutral as2 n2) -> fromMaybe (n1 == n2) ((==) <$> Prelude.lookup n1 env1 <*> Prelude.lookup n2 env2) && length as1 == length as2 && and (Back.zipWith (go i env1 env2) as1 as2)
          _                                  -> False
