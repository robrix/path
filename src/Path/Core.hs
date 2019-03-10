{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, TypeOperators #-}
module Path.Core where

import Control.Monad (ap)
import Data.Foldable (toList)
import qualified Data.Set as Set
import Path.Name
import Path.Plicity
import Path.Usage
import Prelude hiding (pi)
import Text.Trifecta.Rendering (Span)

data Core a
  = Head (Head a)
  | Lam (Scope a)
  | Core a :$ Core a
  | Type
  | Pi Plicity Usage (Core a) (Scope a)
  | Hole a
  | Ann Span (Core a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype Scope a = Scope (Core a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Core where
  pure = Head . Free
  (<*>) = ap

instance Monad Core where
  a >>= f = substIn (const (\case
    Free n -> f n
    Bound i -> Head (Bound i))) a

lam :: Eq a => a -> Core a -> Core a
lam n b = Lam (bind n b)

lams :: (Eq a, Foldable t) => t a -> Core a -> Core a
lams names body = foldr lam body names

pi :: Eq a => (a, Plicity, Usage) ::: Core a -> Core a -> Core a
pi ((n, p, u) ::: t) b = Pi p u t (bind n b)

pis :: (Eq a, Foldable t) => t ((a, Plicity, Usage) ::: Core a) -> Core a -> Core a
pis names body = foldr pi body names

instance Ord a => FreeVariables a (Core a) where
  fvs = \case
    Head h -> fvs h
    Lam (Scope b) -> fvs b
    f :$ a -> fvs f <> fvs a
    Type -> Set.empty
    Pi _ _ t (Scope b) -> fvs t <> fvs b
    Hole v -> Set.singleton v
    Ann _ a -> fvs a

uses :: Gensym -> Core QName -> [Span]
uses n = go Nothing
  where go span = \case
          Head h
            | Free n' <- h, Local n == n' -> toList span
            | otherwise                   -> []
          Lam (Scope b) -> go span b
          f :$ a -> go span f <> go span a
          Type -> []
          Pi _ _ t (Scope b) -> go span t <> go span b
          Hole n'
            | Local n == n' -> toList span
            | otherwise     -> []
          Ann span a -> go (Just span) a


-- | Bind occurrences of a 'Name' in a 'Core' term, producing a 'Scope' in which the 'Name' is bound.
bind :: Eq a => a -> Core a -> Scope a
bind name = Scope . substIn (\ i v -> Head $ case v of
  Bound j -> Bound j
  Free  n -> if name == n then Bound i else Free n)

-- | Substitute a 'Core' term for the free variable in a given 'Scope', producing a closed 'Core' term.
instantiate :: Core a -> Scope a -> Core a
instantiate image (Scope b) = substIn (\ i v -> case v of
  Bound j -> if i == j then image else Head (Bound j)
  Free  n -> pure n) b

substIn :: (Int -> Head a -> Core b)
        -> Core a
        -> Core b
substIn var = go 0
  where go i (Head h)             = var i h
        go i (Lam (Scope b))      = Lam (Scope (go (succ i) b))
        go i (f :$ a)             = go i f :$ go i a
        go _ Type                 = Type
        go i (Pi p u t (Scope b)) = Pi p u (go i t) (Scope (go (succ i) b))
        go i (Hole q)             = var i (Free q)
        go i (Ann s c)            = Ann s (go i c)
