{-# LANGUAGE DeriveTraversable, FlexibleInstances, LambdaCase, MultiParamTypeClasses, TypeOperators #-}
module Path.Surface where

import Path.Core
import Path.Name
import Path.Term
import Path.Usage

type Surface v = Sugar Name :+: Implicit v :+: Core v

data Sugar b a
  = ForAll b a a
  | (Usage, a) :-> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

(-->) :: Semigroup ann => (Usage, Term (Surface v) ann) -> Term (Surface v) ann -> Term (Surface v) ann
(e, a) --> b = In (L ((e, a) :-> b)) (ann a <> ann b)

infixr 0 -->

piType :: Semigroup ann => (Name, Usage, Term (Surface v) ann) -> Term (Surface v) ann -> Term (Surface v) ann
(n, e, a) `piType` b = In (R (R (Pi n e a b))) (ann a <> ann b)

infixr 0 `piType`

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
