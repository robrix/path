{-# LANGUAGE DeriveFunctor, FlexibleInstances #-}
module Path.Surface where

import Data.Bifunctor
import Path.Core
import Path.Name
import Path.Pretty
import Path.Semiring
import Path.Term
import Path.Usage
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

data Surface v a
  = Core (Core v a)
  | a ::: a
  deriving (Eq, Functor, Ord, Show)

instance Bifunctor Surface where
  bimap f g (Core core) = Core (bimap f g core)
  bimap _ g (a ::: t) = g a ::: g t

instance (Pretty v, PrettyPrec a) => PrettyPrec (Surface v a) where
  prettyPrec d (Core core) = prettyPrec d core
  prettyPrec d (tm ::: ty) = prettyParens (d > 0) $ prettyPrec 1 tm <+> pretty ":" <+> prettyPrec 0 ty

(-->) :: Semigroup ann => (Maybe v, Usage, Term (Surface v) ann) -> Term (Surface v) ann -> Term (Surface v) ann
(n, e, a) --> b = In (Core (Pi n e a b)) (ann a <> ann b)

infixr 0 -->

forAll :: Semigroup ann => (Maybe v, Term (Surface v) ann) -> Term (Surface v) ann -> Term (Surface v) ann
forAll (n, a) b = (n, zero, a) --> b

typeT :: Surface v a
typeT = Core Type

var :: v -> Surface v a
var = Core . Var

lam :: Semigroup ann => (Maybe v, ann) -> Term (Surface v) ann -> Term (Surface v) ann
lam (n, a) b = In (Core (Lam n b)) (a <> ann b)

(.:)  :: Semigroup ann => Term (Surface v) ann -> Term (Surface v) ann -> Term (Surface v) ann
a .: t = In (a ::: t) (ann a <> ann t)

(#) :: Semigroup ann => Term (Surface v) ann -> Term (Surface v) ann -> Term (Surface v) ann
f # a = In (Core (f :@ a)) (ann f <> ann a)


subst :: Name -> Surface Name (Term (Surface Name) ann) -> Term (Surface Name) ann -> Term (Surface Name) ann
subst i r (In (e ::: t) ann) = In (subst i r e ::: subst i r t) ann
subst i r (In (Core (Var j)) ann)
  | i == j    = In r ann
  | otherwise = In (Core (Var j)) ann
subst i r (In (Core (Lam n b)) ann)
  | Just i == n = In (Core (Lam n b)) ann
  | otherwise   = In (Core (Lam n (subst i r b))) ann
subst i r (In (Core (f :@ a)) ann) = In (Core (subst i r f :@ subst i r a)) ann
subst _ _ (In (Core Type) ann) = In (Core Type) ann
subst i r (In (Core (Pi n e t t')) ann)
  | Just i == n = In (Core (Pi n e (subst i r t) t')) ann
  | otherwise   = In (Core (Pi n e (subst i r t) (subst i r t'))) ann


uses :: Name -> Term (Surface Name) a -> [a]
uses n = cata $ \ f a -> case f of
  Core (Var n')
    | n == n'   -> [a]
    | otherwise -> []
  Core (Lam n' b)
    | Just n == n' -> []
    | otherwise    -> b
  Core (f :@ a) -> f <> a
  Core Type -> []
  Core (Pi n' _ t b)
    | Just n == n' -> t
    | otherwise    -> t <> b
  a ::: t -> a <> t
