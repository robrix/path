{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, FunctionalDependencies, StandaloneDeriving, UndecidableInstances #-}
module Path.Core where

import Data.Function (fix)
import qualified Data.Set as Set
import Data.Text.Prettyprint.Doc
import Path.FreeVariables
import Path.Name
import Path.Pretty
import Path.Plicity
import Path.Term

data Core a
  = Bound String
  | Free Name
  | Lam String a
  | a :@ a
  | Type
  | Pi String Plicity a a
  deriving (Eq, Functor, Ord, Show)

instance (FreeVariables a, PrettyPrec a) => PrettyPrec (Core a) where
  prettyPrec d c = case c of
    Bound s -> pretty s
    Free (Global s) -> pretty s
    Free (Local s) -> pretty s
    Free (Quote s) -> pretty '\'' <> pretty s
    Lam v b -> prettyParens (d > 0) $ pretty "\\ " <> pretty v <> pretty " . " <> prettyPrec 0 b
    f :@ a -> prettyParens (d > 10) $ prettyPrec 10 f <> pretty ' ' <> prettyPrec 11 a
    Type -> pretty "Type"
    Pi v _ t b
      | Set.member (Local v) (fvs b) -> prettyParens (d > 1) $ prettyBraces True (pretty v <> pretty " : " <> prettyPrec 0 t) <> pretty " -> " <> prettyPrec 1 b
      | otherwise -> prettyPrec 2 t <> pretty " -> " <> prettyPrec 1 b

instance Show (Term Core) where
  showsPrec = fix (\ f d (Term core) -> showCore f fvs d core)

instance FreeVariables1 Core where
  liftFvs _   (Bound s) = Set.singleton (Local s)
  liftFvs _   (Free n) = Set.singleton n
  liftFvs fvs (Lam v b) = Set.delete (Local v) (fvs b)
  liftFvs fvs (f :@ a) = fvs f <> fvs a
  liftFvs _   Type = Set.empty
  liftFvs fvs (Pi v _ t b) = fvs t <> Set.delete (Local v) (fvs b)

instance FreeVariables a => FreeVariables (Core a) where
  fvs = fvs1


fresh :: [String] -> String
fresh [] = "a"
fresh (s:_) = prime s

prime :: String -> String
prime [c] | c < 'z' = [succ c]
prime s = s <> "ʹ"

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
