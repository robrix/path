{-# LANGUAGE DeriveTraversable, FlexibleInstances, LambdaCase, MultiParamTypeClasses, TypeOperators #-}
module Path.Surface where

import Path.Name
import Path.Plicity
import Path.Term
import Path.Usage
import Text.Trifecta.Rendering (Span)

data Surface a
  = Free UName
  | Lam (Maybe UName) a
  | a :$ a
  | Type
  | Pi (Maybe UName) Plicity Usage a a
  | Hole UName
  | (Usage, a) :-> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

(-->) :: (Usage, Term Surface) -> Term Surface -> Term Surface
(e, a) --> b = In ((e, a) :-> b) (ann a <> ann b)

infixr 0 -->

piType :: (Maybe UName, Plicity, Usage, Term Surface) -> Term Surface -> Term Surface
(n, p, e, a) `piType` b = In (Pi n p e a b) (ann a <> ann b)

infixr 0 `piType`

lam :: (Maybe UName, Span) -> Term Surface -> Term Surface
lam (n, a) b = In (Lam n b) (a <> ann b)

($$) :: Term Surface -> Term Surface -> Term Surface
f $$ a = In (f :$ a) (ann f <> ann a)

type' :: Surface a
type' = Type

var :: UName -> Surface a
var = Free

hole :: UName -> Surface a
hole = Hole
