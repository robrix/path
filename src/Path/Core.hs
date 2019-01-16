{-# LANGUAGE FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses #-}
module Path.Core where

import Data.Foldable (toList)
import qualified Data.Set as Set
import Path.Name
import Path.Plicity
import Path.Usage
import Prelude hiding (pi)
import Text.Trifecta.Rendering (Span)

data Core
  = Head (Head QName)
  | Lam Scope
  | Core :$ Core
  | Type
  | Pi Plicity Usage Core Scope
  | Hole QName
  | Ann Span Core
  deriving (Eq, Ord, Show)

newtype Scope = Scope Core
  deriving (Eq, Ord, Show)

free :: QName -> Core
free = Head . Free

lam :: Gensym -> Core -> Core
lam n b = Lam (bind (Local n) b)

lams :: Foldable t => t Gensym -> Core -> Core
lams names body = foldr lam body names

pi :: Gensym -> Plicity -> Usage -> Core -> Core -> Core
pi n p u t b = Pi p u t (bind (Local n) b)

pis :: Foldable t => t (Gensym, Plicity, Usage, Core) -> Core -> Core
pis names body = foldr (\ (n, p, u, t) -> pi n p u t) body names

instance FreeVariables QName Core where
  fvs = \case
    Head h -> fvs h
    Lam (Scope b) -> fvs b
    f :$ a -> fvs f <> fvs a
    Type -> Set.empty
    Pi _ _ t (Scope b) -> fvs t <> fvs b
    Hole v -> Set.singleton v
    Ann _ a -> fvs a

uses :: Gensym -> Core -> [Span]
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
bind :: QName -> Core -> Scope
bind name = Scope . substIn (\ i v -> Head $ case v of
  Bound j -> Bound j
  Free  n -> if name == n then Bound i else Free n)

-- | Substitute a 'Core' term for the free variable in a given 'Scope', producing a closed 'Core' term.
instantiate :: Core -> Scope -> Core
instantiate image (Scope b) = substIn (\ i v -> case v of
  Bound j -> if i == j then image else Head (Bound j)
  Free  n -> free n) b

substIn :: (Int -> Head QName -> Core)
        -> Core
        -> Core
substIn var = go 0
  where go i (Head h)             = var i h
        go i (Lam (Scope b))      = Lam (Scope (go (succ i) b))
        go i (f :$ a)             = go i f :$ go i a
        go _ Type                 = Type
        go i (Pi p u t (Scope b)) = Pi p u (go i t) (Scope (go (succ i) b))
        go _ (Hole q)             = Hole q
        go i (Ann s c)            = Ann s (go i c)
