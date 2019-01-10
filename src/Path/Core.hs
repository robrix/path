{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses #-}
module Path.Core where

import qualified Data.Set as Set
import Path.Name
import Path.Plicity
import Path.Term
import Path.Usage

data Core b v a
  = Free v
  | Bound Int
  | Lam b a
  | a :$ a
  | Type
  | Pi b Plicity Usage a a
  | Hole v
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype Scope a = Scope a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance FreeVariables1 QName (Core Name QName) where
  liftFvs fvs = \case
    Free v -> Set.singleton v
    Bound _ -> Set.empty
    Lam v b -> Set.delete (Local v) (fvs b)
    f :$ a -> fvs f <> fvs a
    Type -> Set.empty
    Pi v _ _ t b -> fvs t <> Set.delete (Local v) (fvs b)
    Hole v -> Set.singleton v

uses :: Name -> Term (Core Name QName) a -> [a]
uses n = cata $ \ f a -> case f of
  Free n'
    | Local n == n' -> [a]
    | otherwise     -> []
  Bound _ -> []
  Lam n' b
    | n == n'   -> []
    | otherwise -> b
  f :$ a -> f <> a
  Type -> []
  Pi n' _ _ t b
    | n == n'   -> t
    | otherwise -> t <> b
  Hole n'
    | Local n == n' -> [a]
    | otherwise     -> []
