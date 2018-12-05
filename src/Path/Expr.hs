{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, FunctionalDependencies, StandaloneDeriving, UndecidableInstances #-}
module Path.Expr where

import Data.Function (fix)
import qualified Data.Set as Set
import Path.Semiring

data Name
  = Global String
  | Local String
  | Quote String
  deriving (Eq, Ord, Show)

data Core a
  = Bound String
  | Free Name
  | Lam String a
  | a :@ a
  | Type
  | Pi String Plicity a a
  deriving (Eq, Functor, Ord, Show)


newtype Term f = Term (f (Term f))

deriving instance Eq (f (Term f)) => Eq (Term f)
deriving instance Ord (f (Term f)) => Ord (Term f)

instance Functor f => Recursive f (Term f) where project (Term f) = f

fresh :: [String] -> String
fresh [] = "a"
fresh (s:_) = prime s

prime :: String -> String
prime [c] | c < 'z' = [succ c]
prime s = s <> "ʹ"

coreFVs :: Core (Set.Set Name) -> Set.Set Name
coreFVs (Bound s) = Set.singleton (Local s)
coreFVs (Free n) = Set.singleton n
coreFVs (Lam v b) = Set.delete (Local v) b
coreFVs (f :@ a) = f <> a
coreFVs Type = Set.empty
coreFVs (Pi v _ t b) = t <> Set.delete (Local v) b

showCore :: (Int -> x -> ShowS) -> (x -> Set.Set Name) -> Int -> Core x -> ShowS
showCore go fvs d c = case c of
  Bound s -> showString s
  Free (Global s) -> showString s
  Free (Local s) -> showString s
  Free (Quote s) -> showChar '\'' . showString s
  Lam v b -> showParen (d > 0) $ showString "\\ " . showString v . showString " -> " . go 0 b
  f :@ a -> showParen (d > 10) $ go 10 f . showChar ' ' . go 11 a
  Type -> showString "Type"
  Pi v _ t b
    | Set.member (Local v) (fvs b) -> showParen (d > 1) $ showBrace True (showString v . showString " : " . go 0 t) . showString " -> " . go 1 b
    | otherwise -> go 2 t . showString " -> " . go 1 b

showBrace :: Bool -> ShowS -> ShowS
showBrace True s = showChar '{' . s . showChar '}'
showBrace False s = s

showCoreTerm :: Int -> Term Core -> ShowS
showCoreTerm = fix (\ f d (Term core) -> showCore f (cata coreFVs) d core)

instance Show (Term Core) where
  showsPrec = showCoreTerm


class Functor f => Recursive f t | t -> f where
  project :: t -> f t

cata :: Recursive f t => (f a -> a) -> t -> a
cata algebra = go
  where go = algebra . fmap go . project


data Plicity = Implicit | Explicit
  deriving (Eq, Ord, Show)

instance Semigroup Plicity where
  Explicit <> _        = Explicit
  _        <> Explicit = Explicit
  _        <> _        = Implicit

instance Monoid Plicity where
  mempty = Implicit

instance Semiring Plicity where
  Implicit >< _        = Implicit
  _        >< Implicit = Implicit
  _        >< _        = Explicit

instance Unital Plicity where
  one = Explicit
