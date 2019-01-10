{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, TypeOperators #-}
module Path.Core where

import qualified Data.Set as Set
import Path.Implicit
import Path.Name
import Path.Plicity
import Path.Term
import Path.Usage

data Core b v a
  = Free v
  | Lam b a
  | a :$ a
  | Type
  | Pi b Plicity Usage a a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data (f :+: g) a
  = L (f a)
  | R (g a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 4 :+:

instance FreeVariables1 QName (Core Name QName) where
  liftFvs fvs = \case
    Free v -> Set.singleton v
    Lam v b -> Set.delete (Local v) (fvs b)
    f :$ a -> fvs f <> fvs a
    Type -> Set.empty
    Pi v _ _ t b -> fvs t <> Set.delete (Local v) (fvs b)

instance (FreeVariables1 v f, FreeVariables1 v g, Ord v) => FreeVariables1 v (f :+: g) where
  liftFvs fvs = \case
    L f -> liftFvs fvs f
    R g -> liftFvs fvs g

uses :: Name -> Term (Implicit QName :+: Core Name QName) a -> [a]
uses n = cata $ \ f a -> case f of
  R (Free n')
    | Local n == n' -> [a]
    | otherwise     -> []
  R (Lam n' b)
    | n == n'   -> []
    | otherwise -> b
  R (f :$ a) -> f <> a
  R Type -> []
  R (Pi n' _ _ t b)
    | n == n'   -> t
    | otherwise -> t <> b
  L (Hole n')
    | Local n == n' -> [a]
    | otherwise     -> []
