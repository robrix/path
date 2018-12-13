{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, StandaloneDeriving, UndecidableInstances #-}
module Path.Core where

import Data.Bifunctor
import qualified Data.Set as Set
import Path.Pretty
import Path.Term
import Path.Usage
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

data Core v a
  = Var v
  | Lam v a
  | a :@ a
  | Type
  | Pi v Usage a a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bifunctor Core where
  bimap f g = \case
    Var v -> Var (f v)
    Lam v a -> Lam (f v) (g a)
    a :@ b -> g a :@ g b
    Type -> Type
    Pi v pi t b -> Pi (f v) pi (g t) (g b)

instance (FreeVariables v a, Pretty v, PrettyPrec a) => PrettyPrec (Core v a) where
  prettyPrec d c = case c of
    Var n -> pretty n
    Lam v b -> prettyParens (d > 0) $ backslash <+> pretty v <+> dot <+> prettyPrec 0 b
    f :@ a -> prettyParens (d > 10) $ prettyPrec 10 f <+> prettyPrec 11 a
    Type -> pretty "Type"
    Pi v pi t b
      | v `Set.member` fvs b -> case pi of
        Zero -> prettyParens (d > 0) $ pretty "∀" <+> pretty v <+> colon <+> prettyPrec 1 t <+> dot <+> prettyPrec 0 b
        _    -> prettyParens (d > 1) $ prettyBraces True (pretty v <+> colon <+> withPi (prettyPrec 0 t)) <+> pretty "->" <+> prettyPrec 1 b
      | otherwise   -> withPi (prettyPrec 2 t <+> pretty "->" <+> prettyPrec 1 b)
      where withPi
              | pi == More = id
              | otherwise  = (pretty pi <+>)

instance Ord v => FreeVariables1 v (Core v) where
  liftFvs fvs = \case
    Var v -> Set.singleton v
    Lam v b -> Set.delete v (fvs b)
    f :@ a -> fvs f <> fvs a
    Type -> Set.empty
    Pi v _ t b -> fvs t <> Set.delete v (fvs b)
