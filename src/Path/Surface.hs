{-# LANGUAGE DeriveTraversable, FlexibleInstances, LambdaCase, MultiParamTypeClasses #-}
module Path.Surface where

import Path.Name
import Path.Subst
import Path.Term
import Path.Usage

data Surface v a
  = Var v
  | Lam Name a
  | a :@ a
  | Type
  | Pi Name Usage a a
  | ForAll Name a a
  | Hole v
  | Implicit
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

(-->) :: Semigroup ann => (Name, Usage, Term (Surface v) ann) -> Term (Surface v) ann -> Term (Surface v) ann
(n, e, a) --> b = In (Pi n e a b) (ann a <> ann b)

infixr 0 -->

forAll :: Semigroup ann => (Name, Term (Surface v) ann) -> Term (Surface v) ann -> Term (Surface v) ann
forAll (n, a) b = In (ForAll n a b) (ann a <> ann b)

lam :: Semigroup ann => (Name, ann) -> Term (Surface v) ann -> Term (Surface v) ann
lam (n, a) b = In (Lam n b) (a <> ann b)

(#) :: Semigroup ann => Term (Surface v) ann -> Term (Surface v) ann -> Term (Surface v) ann
f # a = In (f :@ a) (ann f <> ann a)


instance Substitute QName (Surface QName) where
  subst i r = \case
    In (ForAll v t t') ann
      | i == Local v -> In (ForAll v (subst i r t) t') ann
      | otherwise    -> In (ForAll v (subst i r t) (subst i r t')) ann
    In (Var j) ann
      | i == j    -> In r ann
      | otherwise -> In (Var j) ann
    In (Lam n b) ann
      | i == Local n -> In (Lam n b) ann
      | otherwise    -> In (Lam n (subst i r b)) ann
    In (f :@ a) ann -> In (subst i r f :@ subst i r a) ann
    In Type ann -> In Type ann
    In (Pi n e t t') ann
      | i == Local n -> In (Pi n e (subst i r t) t') ann
      | otherwise    -> In (Pi n e (subst i r t) (subst i r t')) ann
    In (Hole v) ann
      | i == v    -> In r ann
      | otherwise -> In (Hole v) ann
    In Implicit ann -> In Implicit ann


uses :: Name -> Term (Surface QName) a -> [a]
uses n = cata $ \ f a -> case f of
  Var n'
    | Local n == n' -> [a]
    | otherwise     -> []
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
  Hole n'
    | Local n == n' -> [a]
    | otherwise     -> []
  Implicit -> []
