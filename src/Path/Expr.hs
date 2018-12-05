{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, FunctionalDependencies, StandaloneDeriving, UndecidableInstances #-}
module Path.Expr where

import Data.Function (fix)
import qualified Data.Set as Set
import Path.Plicity
import Path.Recursive
import Path.Term

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

instance Show (Term Core) where
  showsPrec = fix (\ f d (Term core) -> showCore f (cata coreFVs) d core)


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
