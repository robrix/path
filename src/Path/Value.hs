{-# LANGUAGE FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses #-}
module Path.Value where

import Data.Foldable (foldl')
import Data.Function (on)
import Path.Back as Back
import qualified Path.Core as Core
import Path.Name
import Path.Plicity
import Path.Pretty
import Path.Term
import Path.Usage

data Value
  = Type                                    -- ^ @'Type' : 'Type'@.
  | Lam                    (Value -> Value) -- ^ A lambda abstraction.
  | Pi Plicity Usage Value (Value -> Value) -- ^ A ∏ type, with a 'Usage' annotation.
  | Back Value :& QName                     -- ^ A neutral term represented as a function on the right and a list of arguments to apply it to in reverse (i.e. &, not $) order.

instance Eq Value where
  (==) = (==) `on` quote 0

instance Ord Value where
  compare = compare `on` quote 0

instance Show Value where
  showsPrec d = showsPrec d . quote 0

instance PrettyPrec Value where
  prettyPrec d = prettyPrec d . quote 0

instance Pretty Value where
  pretty = prettyPrec 0

instance FreeVariables QName Value where
  fvs = fvs . quote 0

vfree :: QName -> Value
vfree = (Nil :&)

vapp :: Value -> Value -> Value
vapp (Lam b) v = b v
vapp (Pi _ _ _ b) v = b v
vapp (vs :& n) v = (vs :> v) :& n
vapp f a = error ("illegal application of " <> show f <> " to " <> show a)


quote :: Int -> Value -> Term (Core.Core Name QName) ()
quote i = \case
  Type -> In Core.Type ()
  Lam b -> In (Core.Lam (Gensym "" i) (quote (succ i) (b (vfree (Local (Gensym "" i)))))) ()
  Pi p u t b -> In (Core.Pi (Gensym "" i) p u (quote i t) (quote (succ i) (b (vfree (Local (Gensym "" i)))))) ()
  sp :& v -> foldr app (In (Core.Var v) ()) sp
  where app a f = In (f Core.:$ quote i a) ()


subst :: QName -> Value -> Value -> Value
subst q r = go
  where go = \case
          Type -> Type
          Lam b -> Lam (go . b)
          Pi p u t b -> Pi p u t (go . b)
          sp :& v
            | q == v    -> foldl' app r sp
            | otherwise -> fmap go sp :& v
            where app f a = f `vapp` go a
