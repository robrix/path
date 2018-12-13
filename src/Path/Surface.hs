{-# LANGUAGE DeriveTraversable, FlexibleInstances, LambdaCase, MultiParamTypeClasses #-}
module Path.Surface where

import Data.Bifunctor
import qualified Data.Set as Set
import Path.Pretty
import Path.Term
import Path.Usage
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

data Surface v a
  = Var v
  | Lam v a
  | a :@ a
  | Type
  | Pi v Usage a a
  | ForAll v a a
  | a ::: a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bifunctor Surface where
  bimap f g = \case
    Var v -> Var (f v)
    Lam v a -> Lam (f v) (g a)
    a :@ b -> g a :@ g b
    Type -> Type
    Pi v pi t b -> Pi (f v) pi (g t) (g b)
    ForAll v t b -> ForAll (f v) (g t) (g b)
    a ::: t -> g a ::: g t

instance (FreeVariables v a, Pretty v, PrettyPrec a) => PrettyPrec (Surface v a) where
  prettyPrec d c = case c of
    Var n -> pretty n
    Lam v b -> prettyParens (d > 0) $ backslash <+> pretty v <+> dot <+> prettyPrec 0 b
    f :@ a -> prettyParens (d > 10) $ prettyPrec 10 f <+> prettyPrec 11 a
    Type -> pretty "Type"
    Pi v pi t b
      | v `Set.member` fvs b -> case pi of
        Zero -> prettyParens (d > 0) $ pretty "∀" <+> pretty v <+> colon <+> prettyPrec 1 t <+> dot <+> prettyPrec 0 b
        _    -> prettyParens (d > 1) $ prettyBraces True (pretty v <+> colon <+> withPi (prettyPrec 0 t)) <+> pretty "->" <+> prettyPrec 1 b
      | otherwise   -> withPi (prettyPrec 2 t <+> pretty "->" <+> prettyPrec 1 b)
      where withPi
              | pi == More = id
              | otherwise  = (pretty pi <+>)
    ForAll v t b -> prettyParens (d > 0) $ pretty "∀" <+> pretty v <+> colon <+> prettyPrec 1 t <+> dot <+> prettyPrec 0 b
    tm ::: ty -> prettyParens (d > 0) $ prettyPrec 1 tm <+> pretty ":" <+> prettyPrec 0 ty

(-->) :: Semigroup ann => (v, Usage, Term (Surface v) ann) -> Term (Surface v) ann -> Term (Surface v) ann
(n, e, a) --> b = In (Pi n e a b) (ann a <> ann b)

infixr 0 -->

forAll :: Semigroup ann => (v, Term (Surface v) ann) -> Term (Surface v) ann -> Term (Surface v) ann
forAll (n, a) b = In (ForAll n a b) (ann a <> ann b)

typeT :: Surface v a
typeT = Type

var :: v -> Surface v a
var = Var

lam :: Semigroup ann => (v, ann) -> Term (Surface v) ann -> Term (Surface v) ann
lam (n, a) b = In (Lam n b) (a <> ann b)

(.:)  :: Semigroup ann => Term (Surface v) ann -> Term (Surface v) ann -> Term (Surface v) ann
a .: t = In (a ::: t) (ann a <> ann t)

(#) :: Semigroup ann => Term (Surface v) ann -> Term (Surface v) ann -> Term (Surface v) ann
f # a = In (f :@ a) (ann f <> ann a)


subst :: Eq v => v -> Surface v (Term (Surface v) ann) -> Term (Surface v) ann -> Term (Surface v) ann
subst i r (In (e ::: t) ann) = In (subst i r e ::: subst i r t) ann
subst i r (In (ForAll v t t') ann)
  | i == v    = In (ForAll v (subst i r t) t') ann
  | otherwise = In (ForAll v (subst i r t) (subst i r t')) ann
subst i r (In (Var j) ann)
  | i == j    = In r ann
  | otherwise = In (Var j) ann
subst i r (In (Lam n b) ann)
  | i == n    = In (Lam n b) ann
  | otherwise = In (Lam n (subst i r b)) ann
subst i r (In (f :@ a) ann) = In (subst i r f :@ subst i r a) ann
subst _ _ (In Type ann) = In Type ann
subst i r (In (Pi n e t t') ann)
  | i == n    = In (Pi n e (subst i r t) t') ann
  | otherwise = In (Pi n e (subst i r t) (subst i r t')) ann


uses :: Eq v => v -> Term (Surface v) a -> [a]
uses n = cata $ \ f a -> case f of
  Var n'
    | n == n'   -> [a]
    | otherwise -> []
  Lam n' b
    | n == n'   -> []
    | otherwise -> b
  f :@ a -> f <> a
  Type -> []
  Pi n' _ t b
    | n == n'   -> t
    | otherwise -> t <> b
  ForAll n' t b
    | n == n'   -> t
    | otherwise -> t <> b
  a ::: t -> a <> t

instance Ord v => FreeVariables1 v (Surface v) where
  liftFvs fvs = \case
    Var v -> Set.singleton v
    Lam v b -> Set.delete v (fvs b)
    f :@ a -> fvs f <> fvs a
    Type -> Set.empty
    Pi v _ t b -> fvs t <> Set.delete v (fvs b)
    ForAll v t b -> fvs t <> Set.delete v (fvs b)
    a ::: t -> fvs a <> fvs t
