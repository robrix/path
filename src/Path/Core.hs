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
  = Free QName
  | Bound Int
  | Lam Scope
  | Core :$ Core
  | Type
  | Pi Plicity Usage Core (Scope)
  | Hole QName
  | Ann Span Core
  deriving (Eq, Ord, Show)

newtype Scope = Scope Core
  deriving (Eq, Ord, Show)

lam :: Name -> Core -> Core
lam n b = Lam (bind (Local n) b)

lams :: Foldable t => t Name -> Core -> Core
lams names body = foldr lam body names

pi :: Name -> Plicity -> Usage -> Core -> Core -> Core
pi n p u t b = Pi p u t (bind (Local n) b)

pis :: Foldable t => t (Name, Plicity, Usage, Core) -> Core -> Core
pis names body = foldr (\ (n, p, u, t) -> pi n p u t) body names

instance FreeVariables QName Core where
  fvs = \case
    Free v -> Set.singleton v
    Bound _ -> Set.empty
    Lam (Scope b) -> fvs b
    f :$ a -> fvs f <> fvs a
    Type -> Set.empty
    Pi _ _ t (Scope b) -> fvs t <> fvs b
    Hole v -> Set.singleton v
    Ann _ a -> fvs a

uses :: Name -> Core -> [Span]
uses n = go Nothing
  where go span = \case
          Free n'
            | Local n == n' -> toList span
            | otherwise     -> []
          Bound _ -> []
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
bind name = Scope . substIn (\ i v -> case v of
  Left  j -> Bound j
  Right n -> if name == n then Bound i else Free n)

-- | Substitute a 'Core' term for the free variable in a given 'Scope', producing a closed 'Core' term.
instantiate :: Core -> Scope -> Core
instantiate image (Scope b) = substIn (\ i v -> case v of
  Left  j -> if i == j then image else Bound j
  Right n -> Free n) b

substIn :: (Int -> Either Int QName -> Core)
        -> Core
        -> Core
substIn var = go 0
  where go i (Free n)             = var i (Right n)
        go i (Bound j)            = var i (Left j)
        go i (Lam (Scope b))      = Lam (Scope (go (succ i) b))
        go i (f :$ a)             = go i f :$ go i a
        go _ Type                 = Type
        go i (Pi p u t (Scope b)) = Pi p u (go i t) (Scope (go (succ i) b))
        go _ (Hole q)             = Hole q
        go i (Ann s c)            = Ann s (go i c)
