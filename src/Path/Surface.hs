{-# LANGUAGE DeriveTraversable, FlexibleInstances, LambdaCase, MultiParamTypeClasses, TypeOperators #-}
module Path.Surface where

import Path.Core
import Path.Name
import Path.Term
import Path.Usage

type Surface v = Sugar v :+: Implicit v :+: Core v

data Sugar v a
  = ForAll Name a a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

(-->) :: Semigroup ann => (Name, Usage, Term (Surface v) ann) -> Term (Surface v) ann -> Term (Surface v) ann
(n, e, a) --> b = In (R (R (Pi n e a b))) (ann a <> ann b)

infixr 0 -->

forAll :: Semigroup ann => (Name, Term (Surface v) ann) -> Term (Surface v) ann -> Term (Surface v) ann
forAll (n, a) b = In (L (ForAll n a b)) (ann a <> ann b)

lam :: Semigroup ann => (Name, ann) -> Term (Surface v) ann -> Term (Surface v) ann
lam (n, a) b = In (R (R (Lam n b))) (a <> ann b)

(#) :: Semigroup ann => Term (Surface v) ann -> Term (Surface v) ann -> Term (Surface v) ann
f # a = In (R (R (f :@ a))) (ann f <> ann a)

type' :: Surface v a
type' = R (R Type)

implicit :: Surface v a
implicit = R (L Implicit)

var :: v -> Surface v a
var = R . R . Var

hole :: v -> Surface v a
hole = R . L . Hole


uses :: Name -> Term (Surface QName) a -> [a]
uses n = cata $ \ f a -> case f of
  R (R (Var n'))
    | Local n == n' -> [a]
    | otherwise     -> []
  R (R (Lam n' b))
    | n == n'   -> []
    | otherwise -> b
  R (R (f :@ a)) -> f <> a
  R (R Type) -> []
  R (R (Pi n' _ t b))
    | n == n'   -> t
    | otherwise -> t <> b
  L (ForAll n' t b)
    | n == n'   -> t
    | otherwise -> t <> b
  R (L (Hole n'))
    | Local n == n' -> [a]
    | otherwise     -> []
  R (L Implicit) -> []
