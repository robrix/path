{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, FunctionalDependencies, LambdaCase, StandaloneDeriving, UndecidableInstances #-}
module Path.Core where

import Data.Bifunctor
import qualified Data.Set as Set
import Path.FreeVariables
import Path.Name
import Path.Pretty
import Path.Usage
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

data Core v a
  = Var v
  | Lam (Maybe v) a
  | a :@ a
  | Type
  | Pi (Maybe v) Usage a a
  deriving (Eq, Functor, Ord, Show)

instance Bifunctor Core where
  bimap f g = \case
    Var v -> Var (f v)
    Lam v a -> Lam (f <$> v) (g a)
    a :@ b -> g a :@ g b
    Type -> Type
    Pi v pi t b -> Pi (f <$> v) pi (g t) (g b)

instance PrettyPrec a => PrettyPrec (Core Name a) where
  prettyPrec d c = case c of
    Var n -> pretty n
    Lam v b -> prettyParens (d > 0) $ backslash <+> pretty v <+> dot <+> prettyPrec 0 b
    f :@ a -> prettyParens (d > 10) $ prettyPrec 10 f <+> prettyPrec 11 a
    Type -> pretty "Type"
    Pi v pi t b
      | Just v <- v -> case pi of
        Zero -> prettyParens (d > 0) $ pretty "∀" <+> pretty v <+> colon <+> prettyPrec 1 t <+> dot <+> prettyPrec 0 b
        _    -> prettyParens (d > 1) $ prettyBraces True (pretty v <+> colon <+> withPi (prettyPrec 0 t)) <+> pretty "->" <+> prettyPrec 1 b
      | otherwise   -> withPi (prettyPrec 2 t <+> pretty "->" <+> prettyPrec 1 b)
      where withPi
              | pi == More = id
              | otherwise  = (pretty pi <+>)

instance FreeVariables1 (Core Name) where
  liftFvs _   (Var n) = Set.singleton n
  liftFvs fvs (Lam v b) = maybe id Set.delete v (fvs b)
  liftFvs fvs (f :@ a) = fvs f <> fvs a
  liftFvs _   Type = Set.empty
  liftFvs fvs (Pi v _ t b) = fvs t <> maybe id Set.delete v (fvs b)

instance FreeVariables a => FreeVariables (Core Name a) where
  fvs = fvs1
