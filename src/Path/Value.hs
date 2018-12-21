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
  | VNeutral (Neutral v)

instance Ord v => Eq (Value v) where
  (==) = (==) `on` quote const

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
vfree = VNeutral . NFree

data Neutral v
  = NFree v
  | NApp (Neutral v) (Value v)

quote :: (Int -> v -> u) -> Value v -> Term (Core u) ()
quote f = go 0
  where go i = \case
          VType -> In Type ()
          VLam n b -> In (Lam (f i n) (go (succ i) (b (vfree n)))) ()
          VPi n e t b -> In (Pi (f i n) e (go i t) (go (succ i) (b (vfree n)))) ()
          VNeutral n -> goN i n

        goN i (NFree n) = In (Var (f i n)) ()
        goN i (NApp n a) = In (goN i n :@ go i a) ()

aeq :: Eq v => Value v -> Value v -> Bool
aeq = go (0 :: Int) [] []
  where go i env1 env2 v1 v2 = case (v1, v2) of
          (VType,           VType)           -> True
          (VLam n1 b1,      VLam n2 b2)      -> go (succ i) ((n1, i) : env1) ((n2, i) : env2) (b1 (vfree n1)) (b2 (vfree n2))
          (VPi n1 e1 t1 b1, VPi n2 e2 t2 b2) -> e1 == e2 && go i env1 env2 t1 t2 && go (succ i) ((n1, i) : env1) ((n2, i) : env2) (b1 (vfree n1)) (b2 (vfree n2))
          (VNeutral n1,     VNeutral n2)     -> goN i env1 env2 n1 n2
          _                                  -> False

        goN i env1 env2 n1 n2 = case (n1, n2) of
          (NFree n1,   NFree n2)   -> fromMaybe (n1 == n2) ((==) <$> lookup n1 env1 <*> lookup n2 env2)
          (NApp n1 a1, NApp n2 a2) -> goN i env1 env2 n1 n2 && go i env1 env2 a1 a2
          _                        -> False
