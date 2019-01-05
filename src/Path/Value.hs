{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses #-}
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
  | QName :$ Back Value                     -- ^ A neutral term represented as a function on the right and a list of arguments to apply it.

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
vfree = (:$ Nil)

($$) :: Value -> Value -> Value
Lam b      $$ v = b v
Pi _ _ _ b $$ v = b v
n :$ vs    $$ v = n :$ (vs :> v)
f          $$ v = error ("illegal application of " <> show (plain (pretty f)) <> " to " <> show (plain (pretty v)))

($$*) :: Foldable t => Value -> t Value -> Value
v $$* sp = foldl' ($$) v sp


-- | Quote a 'Value', producing an equivalent 'Term'.
--
--   prop> quote i Type == In Core.Type ()
--   prop> quote i (Lam id) == In (Core.Lam (Gensym "" i) (In (Core.Var (Local (Gensym "" i))) ())) ()
--   prop> quote i (Pi Im Zero Type id) == In (Core.Pi (Gensym "" i) Im Zero (In Core.Type ()) (In (Core.Var (Local (Gensym "" i))) ())) ()
--   prop> quote i ((vfree (Local (Name s)) $$ vfree (Local (Name t))) $$ vfree (Local (Name u))) == In (In (In (Core.Var (Local (Name s))) () Core.:$ In (Core.Var (Local (Name t))) ()) () Core.:$ In (Core.Var (Local (Name u))) ()) ()
quote :: Int -> Value -> Term (Core.Core Name QName) ()
quote i = \case
  Type -> In Core.Type ()
  Lam b -> In (Core.Lam (Gensym "" i) (quote (succ i) (b (vfree (Local (Gensym "" i)))))) ()
  Pi p u t b -> In (Core.Pi (Gensym "" i) p u (quote i t) (quote (succ i) (b (vfree (Local (Gensym "" i)))))) ()
  v :$ sp -> foldl' app (In (Core.Var v) ()) sp
  where app f a = In (f Core.:$ quote i a) ()


-- | Substitute occurrences of a 'QName' with a 'Value' within another 'Value'.
--
--   prop> subst (Local (Name a)) (vfree (Local (Name b))) (Lam ($$ vfree (Local (Name a)))) == Lam ($$ vfree (Local (Name b)))
subst :: QName -> Value -> Value -> Value
subst q r = go
  where go = \case
          Type -> Type
          Lam b -> Lam (go . b)
          Pi p u t b -> Pi p u (go t) (go . b)
          v :$ sp
            | q == v    -> r $$* (go <$> sp)
            | otherwise -> v :$ fmap go sp

generalizeType :: Value -> Value
generalizeType ty = foldr bind ty (localNames (fvs ty))
  where bind n b = Pi Im Zero Type (flip (subst (Local n)) b)

generalizeValue :: Value -> Value -> Value
generalizeValue = go 0
  where go i (Pi Im _ _ b) v = Lam (const (go (succ i) (b (vfree (Local (Gensym "" i)))) v))
        go _ _             v = v

split :: Value -> (Value, Back Value)
split (v :$ vs) = (vfree v, vs)
split v         = (v, Nil)


type Type = Value

data Typed a = a ::: Type
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

typedTerm :: Typed a -> a
typedTerm (a ::: _) = a

typedType :: Typed a -> Type
typedType (_ ::: t) = t

infix 6 :::

instance Pretty a => Pretty (Typed a) where
  pretty (a ::: t) = pretty a <+> colon <+> pretty t

instance Pretty a => PrettyPrec (Typed a)
