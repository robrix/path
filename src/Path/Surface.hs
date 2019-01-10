{-# LANGUAGE DeriveTraversable, FlexibleInstances, LambdaCase, MultiParamTypeClasses, TypeOperators #-}
module Path.Surface where

import Path.Name
import Path.Plicity
import Path.Term
import Path.Usage
import Text.Trifecta.Rendering (Span)

data Surface b v a
  = Free v
  | Lam b a
  | a :$ a
  | Type
  | Pi b Plicity Usage a a
  | Hole v
  | (Usage, a) :-> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

(-->) :: (Usage, Term (Surface (Maybe UName) v)) -> Term (Surface (Maybe UName) v) -> Term (Surface (Maybe UName) v)
(e, a) --> b = In ((e, a) :-> b) (ann a <> ann b)

infixr 0 -->

piType :: (Maybe UName, Plicity, Usage, Term (Surface (Maybe UName) v)) -> Term (Surface (Maybe UName) v) -> Term (Surface (Maybe UName) v)
(n, p, e, a) `piType` b = In (Pi n p e a b) (ann a <> ann b)

infixr 0 `piType`

lam :: (Maybe UName, Span) -> Term (Surface (Maybe UName) v) -> Term (Surface (Maybe UName) v)
lam (n, a) b = In (Lam n b) (a <> ann b)

($$) :: Term (Surface (Maybe UName) v) -> Term (Surface (Maybe UName) v) -> Term (Surface (Maybe UName) v)
f $$ a = In (f :$ a) (ann f <> ann a)

type' :: Surface b v a
type' = Type

var :: v -> Surface b v a
var = Free

hole :: v -> Surface b v a
hole = Hole
