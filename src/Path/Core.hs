{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, StandaloneDeriving, UndecidableInstances #-}
module Path.Core where

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

instance (FreeVariables v a, Pretty v, PrettyPrec a) => PrettyPrec (Core v (Term (Core v) a)) where
  prettyPrec d c = case c of
    Var n -> pretty n
    Lam v b -> prettyParens (d > 0) $ align (group (cyan backslash <+> go v b))
      where go v b = var v b <> case b of
              In (Lam v' b') _ -> space <> go v' b'
              _                -> line <> cyan dot <+> prettyPrec 0 b
            var v b | v `Set.member` fvs b = pretty v
                    | otherwise            = pretty '_'
    f :@ a -> prettyParens (d > 10) $ group (align (nest 2 (go f a)))
      where go f a = case f of
              In (f' :@ a') _ -> go f' a' </> prettyPrec 11 a
              _               -> prettyPrec 10 f </> prettyPrec 11 a
    Type -> yellow (pretty "Type")
    Pi v pi t b
      | v `Set.member` fvs b -> case pi of
        Zero -> prettyParens (d > 1) $ align (group (cyan (pretty "∀") <+> pretty v <+> colon <+> prettyPrec 2 t <> line <> cyan dot <+> prettyPrec 1 b))
        _    -> prettyParens (d > 1) $ prettyBraces True (pretty v <+> colon <+> withPi (prettyPrec 0 t)) <+> arrow <+> prettyPrec 1 b
      | otherwise   -> prettyParens (d > 1) $ withPi (prettyPrec 2 t <+> arrow <+> prettyPrec 1 b)
      where withPi
              | pi == More = id
              | otherwise  = (pretty pi <+>)
            arrow = blue (pretty "->")

instance Ord v => FreeVariables1 v (Core v) where
  liftFvs fvs = \case
    Var v -> Set.singleton v
    Lam v b -> Set.delete v (fvs b)
    f :@ a -> fvs f <> fvs a
    Type -> Set.empty
    Pi v _ t b -> fvs t <> Set.delete v (fvs b)
