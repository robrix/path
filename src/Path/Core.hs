{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, FunctionalDependencies, StandaloneDeriving, UndecidableInstances #-}
module Path.Core where

import qualified Data.Set as Set
import Path.FreeVariables
import Path.Name
import Path.Pretty
import Path.Usage
import Text.PrettyPrint.ANSI.Leijen

data Core a
  = Var Name
  | Lam String a
  | a :@ a
  | Type
  | Pi String Usage a a
  deriving (Eq, Functor, Ord, Show)

instance (FreeVariables a, PrettyPrec a) => PrettyPrec (Core a) where
  prettyPrec d c = case c of
    Var n -> pretty n
    Lam v b -> prettyParens (d > 0) $ backslash <+> pretty v <+> dot <+> prettyPrec 0 b
    f :@ a -> prettyParens (d > 10) $ prettyPrec 10 f <+> prettyPrec 11 a
    Type -> pretty "Type"
    Pi v pi t b
      | Set.member (Local v) (fvs b) -> prettyParens (d > 1) $ prettyBraces True (pretty v <+> pretty ":" <+> withPi (prettyPrec 0 t)) <+> pretty "->" <+> prettyPrec 1 b
      | otherwise -> withPi (prettyPrec 2 t <+> pretty "->" <+> prettyPrec 1 b)
      where withPi
              | pi == More = id
              | otherwise  = (pretty pi <+>)

instance FreeVariables1 Core where
  liftFvs _   (Var n) = Set.singleton n
  liftFvs fvs (Lam v b) = Set.delete (Local v) (fvs b)
  liftFvs fvs (f :@ a) = fvs f <> fvs a
  liftFvs _   Type = Set.empty
  liftFvs fvs (Pi v _ t b) = fvs t <> Set.delete (Local v) (fvs b)

instance FreeVariables a => FreeVariables (Core a) where
  fvs = fvs1
