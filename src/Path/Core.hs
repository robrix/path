{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses #-}
module Path.Core where

import qualified Data.Set as Set
import Path.Name
import Path.Plicity
import Path.Term
import Path.Usage
import Text.Trifecta.Rendering (Span)

data Core b v a
  = Free v
  | Bound Int
  | Lam b (Scope a)
  | a :$ a
  | Type
  | Pi b Plicity Usage a (Scope a)
  | Hole v
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype Scope a = Scope a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance FreeVariables1 QName (Core Name QName) where
  liftFvs fvs = \case
    Free v -> Set.singleton v
    Bound _ -> Set.empty
    Lam v (Scope b) -> Set.delete (Local v) (fvs b)
    f :$ a -> fvs f <> fvs a
    Type -> Set.empty
    Pi v _ _ t (Scope b) -> fvs t <> Set.delete (Local v) (fvs b)
    Hole v -> Set.singleton v

uses :: Name -> Term (Core Name QName) -> [Span]
uses n = cata $ \ f a -> case f of
  Free n'
    | Local n == n' -> [a]
    | otherwise     -> []
  Bound _ -> []
  Lam n' (Scope b)
    | n == n'   -> []
    | otherwise -> b
  f :$ a -> f <> a
  Type -> []
  Pi n' _ _ t (Scope b)
    | n == n'   -> t
    | otherwise -> t <> b
  Hole n'
    | Local n == n' -> [a]
    | otherwise     -> []
