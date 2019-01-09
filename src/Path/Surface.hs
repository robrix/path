{-# LANGUAGE DeriveTraversable, FlexibleInstances, LambdaCase, MultiParamTypeClasses, TypeOperators #-}
module Path.Surface where

import Path.Name
import Path.Plicity
import Path.Term
import Path.Usage

data Surface b v a
  = Free v
  | Lam b a
  | a :$ a
  | Type
  | Pi b Plicity Usage a a
  | Hole v
  | (Usage, a) :-> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

(-->) :: Semigroup ann => (Usage, Term (Surface (Maybe Name) v) ann) -> Term (Surface (Maybe Name) v) ann -> Term (Surface (Maybe Name) v) ann
(e, a) --> b = In ((e, a) :-> b) (ann a <> ann b)

infixr 0 -->

piType :: Semigroup ann => (Maybe Name, Plicity, Usage, Term (Surface (Maybe Name) v) ann) -> Term (Surface (Maybe Name) v) ann -> Term (Surface (Maybe Name) v) ann
(n, p, e, a) `piType` b = In (Pi n p e a b) (ann a <> ann b)

infixr 0 `piType`

lam :: Semigroup ann => (Maybe Name, ann) -> Term (Surface (Maybe Name) v) ann -> Term (Surface (Maybe Name) v) ann
lam (n, a) b = In (Lam n b) (a <> ann b)

($$) :: Semigroup ann => Term (Surface (Maybe Name) v) ann -> Term (Surface (Maybe Name) v) ann -> Term (Surface (Maybe Name) v) ann
f $$ a = In (f :$ a) (ann f <> ann a)

type' :: Surface b v a
type' = Type

var :: v -> Surface b v a
var = Free

hole :: v -> Surface b v a
hole = Hole
