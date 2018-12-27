{-# LANGUAGE DeriveTraversable, FlexibleInstances, LambdaCase, MultiParamTypeClasses #-}
module Path.Surface where

import Path.Name
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

data Sugar v a
  = ForAll' Name a a
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
