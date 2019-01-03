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

($$) :: Value -> Value -> Value
Lam b $$  v = b v
Pi _ _ _ b $$ v = b v
vs :& n $$ v = (vs :> v) :& n
f $$ a = error ("illegal application of " <> show (plain (pretty f)) <> " to " <> show (plain (pretty a)))

($$*) :: Value -> Back Value -> Value
v $$* sp = foldl' ($$) v sp


-- | Quote a 'Value', producing an equivalent 'Term'.
--
--   prop> quote i Type == In Core.Type ()
--   prop> quote i (Lam id) == In (Core.Lam (Gensym "" i) (In (Core.Var i) ())) ()
--   prop> quote i (Pi Im Zero Type id) == In (Core.Pi Im Zero Type (Gensym "" i) (In (Core.Var i) ())) ()
--   prop> quote i ((vfree (Local (Name s)) $$ vfree (Local (Name t))) $$ vfree (Local (Name u))) == In (In (In (Core.Var (Local (Name s))) () Core.:$ In (Core.Var (Local (Name t))) ()) () :$ In (Core.Var (Local (Name u))) ()) ()
quote :: Int -> Value -> Term (Core.Core Name QName) ()
quote i = \case
  Type -> In Core.Type ()
  Lam b -> In (Core.Lam (Gensym "" i) (quote (succ i) (b (vfree (Local (Gensym "" i)))))) ()
  Pi p u t b -> In (Core.Pi (Gensym "" i) p u (quote i t) (quote (succ i) (b (vfree (Local (Gensym "" i)))))) ()
  sp :& v -> foldr app (In (Core.Var v) ()) sp
  where app a f = In (f Core.:$ quote i a) ()


-- | Substitute occurrences of a 'QName' with a 'Value' within another 'Value'.
--
--   prop> subst (Local (Name a)) (vfree (Local (Name b))) (Lam ($$ vfree (Local (Name a)))) == Lam ($$ vfree (Local (Name b)))
subst :: QName -> Value -> Value -> Value
subst q r = go
  where go = \case
          Type -> Type
          Lam b -> Lam (go . b)
          Pi p u t b -> Pi p u (go t) (go . b)
          sp :& v
            | q == v    -> r $$* (go <$> sp)
            | otherwise -> fmap go sp :& v

generalizeType :: Value -> Value
generalizeType ty = foldr bind ty (localNames (fvs ty))
  where bind n b = Pi Im Zero Type (flip (subst (Local n)) b)

generalizeValue :: Value -> Value -> Value
generalizeValue = go 0
  where go i (Pi Im _ _ b) v = Lam (const (go (succ i) (b (vfree (Local (Gensym "" i)))) v))
        go _ _             v = v


-- $setup
--
-- >>> import Test.QuickCheck
