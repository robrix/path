{-# LANGUAGE FlexibleInstances, LambdaCase, MultiParamTypeClasses #-}
module Path.Value where

import Data.Foldable (foldl')
import Data.Function (on)
import Data.Maybe (fromMaybe)
import Path.Back as Back
import qualified Path.Core as Core
import Path.Name
import Path.Pretty
import Path.Term
import Path.Usage
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

data Value v
  = Type                                       -- ^ @'Type' : 'Type'@.
  | Lam v                 (Value v -> Value v) -- ^ A HOAS-encoded lambda abstraction.
  | Pi  v Usage (Value v) (Value v -> Value v) -- ^ A HOAS-encoded ∏ type, with a 'Usage' annotation.
  | Neutral (Back (Value v)) v                 -- ^ A neutral term represented as a function on the right and a list of arguments to apply it to in reverse (i.e. &, not $) order.

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
vfree = Neutral Nil

vapp :: Show v => Value v -> Value v -> Value v
vapp (Lam _ f) v = f v
vapp (Neutral vs n) v = Neutral (vs :> v) n
vapp f a = error ("illegal application of " <> show f <> " to " <> show a)


quote :: (Int -> v -> u) -> Value v -> Term (Core.Core u) ()
quote f = go 0
  where go i = \case
          Type         -> In Core.Type ()
          Lam n b      -> In (Core.Lam (f i n) (go (succ i) (b (vfree n)))) ()
          Pi n e t b   -> In (Core.Pi (f i n) e (go i t) (go (succ i) (b (vfree n)))) ()
          Neutral as n -> foldl' app (In (Core.Var (f i n)) ()) as
          where app f a = In (f Core.:@ go i a) ()

aeq :: Eq v => Value v -> Value v -> Bool
aeq = go (0 :: Int) [] []
  where go i env1 env2 v1 v2 = case (v1, v2) of
          (Type,           Type)           -> True
          (Lam n1 b1,      Lam n2 b2)      -> go (succ i) ((n1, i) : env1) ((n2, i) : env2) (b1 (vfree n1)) (b2 (vfree n2))
          (Pi n1 e1 t1 b1, Pi n2 e2 t2 b2) -> e1 == e2 && go i env1 env2 t1 t2 && go (succ i) ((n1, i) : env1) ((n2, i) : env2) (b1 (vfree n1)) (b2 (vfree n2))
          (Neutral as1 n1, Neutral as2 n2) -> fromMaybe (n1 == n2) ((==) <$> Prelude.lookup n1 env1 <*> Prelude.lookup n2 env2) && length as1 == length as2 && and (Back.zipWith (go i env1 env2) as1 as2)
          _                                -> False
