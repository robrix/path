{-# LANGUAGE DeriveFunctor, FlexibleInstances #-}
module Path.Surface where

import Path.Core
import Path.FreeVariables
import Path.Name
import Path.Pretty
import Path.Semiring
import Path.Term
import Path.Usage
import Text.PrettyPrint.ANSI.Leijen

data Surface a
  = Core (Core a)
  | a ::: a
  deriving (Eq, Functor, Ord, Show)

instance (FreeVariables a, PrettyPrec a) => PrettyPrec (Surface a) where
  prettyPrec d (Core core) = prettyPrec d core
  prettyPrec d (tm ::: ty) = prettyParens (d > 0) $ prettyPrec 1 tm <+> pretty ":" <+> prettyPrec 0 ty

instance FreeVariables1 Surface where
  liftFvs fvs (Core core) = liftFvs fvs core
  liftFvs fvs (tm ::: ty) = fvs tm <> fvs ty

instance FreeVariables a => FreeVariables (Surface a) where
  fvs = fvs1

(-->) :: Semigroup ann => (String, Usage, Term Surface ann) -> Term Surface ann -> Term Surface ann
(n, e, a) --> b = In (Core (Pi n e a b)) (ann a <> ann b)

infixr 0 -->

forAll :: Semigroup ann => (String, Term Surface ann) -> Term Surface ann -> Term Surface ann
forAll (n, a) b = (n, zero, a) --> b

typeT :: Surface a
typeT = Core Type

global :: String -> Surface a
global = Core . Var . Global

var :: String -> Surface a
var = Core . Var . Local

lam :: Semigroup ann => (String, ann) -> Term Surface ann -> Term Surface ann
lam (n, a) b = In (Core (Lam n b)) (a <> ann b)

(.:)  :: Semigroup ann => Term Surface ann -> Term Surface ann -> Term Surface ann
a .: t = In (a ::: t) (ann a <> ann t)

(#) :: Semigroup ann => Term Surface ann -> Term Surface ann -> Term Surface ann
f # a = In (Core (f :@ a)) (ann f <> ann a)


subst :: String -> Surface (Term Surface ann) -> Term Surface ann -> Term Surface ann
subst i r (In (e ::: t) ann) = In (subst i r e ::: subst i r t) ann
subst i r (In (Core (Var j)) ann)
  | Local i == j = In r ann
  | otherwise    = In (Core (Var j)) ann
subst i r (In (Core (Lam n b)) ann)
  | i == n    = In (Core (Lam n b)) ann
  | otherwise = In (Core (Lam n (subst i r b))) ann
subst i r (In (Core (f :@ a)) ann) = In (Core (subst i r f :@ subst i r a)) ann
subst _ _ (In (Core Type) ann) = In (Core Type) ann
subst i r (In (Core (Pi n e t t')) ann)
  | i == n    = In (Core (Pi n e (subst i r t) t')) ann
  | otherwise = In (Core (Pi n e (subst i r t) (subst i r t'))) ann


uses :: Name -> Term Surface a -> [a]
uses n = cata $ \ f a -> case f of
  Core (Var n')
    | n == n'   -> [a]
    | otherwise -> []
  Core (Lam n' b)
    | n == Local n' -> []
    | otherwise     -> b
  Core (f :@ a) -> f <> a
  Core Type -> []
  Core (Pi n' _ t b)
    | n == Local n' -> t
    | otherwise     -> t <> b
  a ::: t -> a <> t
