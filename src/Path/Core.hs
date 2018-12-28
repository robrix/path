{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, TypeOperators #-}
module Path.Core where

import qualified Data.Set as Set
import Path.Name
import Path.Plicity
import Path.Pretty
import Path.Term
import Path.Usage

data Core b v a
  = Var v
  | Lam b a
  | a :$ a
  | Type
  | Pi b Plicity Usage a a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data (f :+: g) a
  = L (f a)
  | R (g a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 4 :+:

data Implicit v a
  = Hole v
  | Implicit
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance (FreeVariables QName a, PrettyPrec a) => PrettyPrec (Core Name QName (Term (Core Name QName) a)) where
  prettyPrec d = \case
    Var n -> pretty n
    Lam v b -> prettyParens (d > 0) $ align (group (cyan backslash <+> go v b))
      where go v b = var v b <> case b of
              In (Lam v' b') _ -> space <> go v' b'
              _                -> line <> cyan dot <+> prettyPrec 0 b
            var v b | Local v `Set.member` fvs b = pretty v
                    | otherwise                  = pretty '_'
    f :$ a -> prettyParens (d > 10) $ group (align (nest 2 (go f a)))
      where go f a = case f of
              In (f' :$ a') _ -> go f' a' </> prettyPrec 11 a
              _               -> prettyPrec 10 f </> prettyPrec 11 a
    Type -> yellow (pretty "Type")
    Pi v ie pi t b
      | Local v `Set.member` fvs b -> case pi of
        Zero -> prettyParens (d > 1) $ align (group (cyan (pretty "∀") <+> pretty v <+> colon <+> prettyPrec 2 t <> line <> cyan dot <+> prettyPrec 1 b))
        _    -> prettyParens (d > 1) $ withIe (pretty v <+> colon <+> withPi (prettyPrec 0 t)) <+> arrow <+> prettyPrec 1 b
      | otherwise                  -> prettyParens (d > 1) $ withPi (prettyPrec 2 t <+> arrow <+> prettyPrec 1 b)
      where withPi
              | pi == More = id
              | otherwise  = (pretty pi <+>)
            withIe
              | ie == Im  = prettyBraces True
              | otherwise = prettyParens True
            arrow = blue (pretty "->")

instance FreeVariables1 QName (Core Name QName) where
  liftFvs fvs = \case
    Var v -> Set.singleton v
    Lam v b -> Set.delete (Local v) (fvs b)
    f :$ a -> fvs f <> fvs a
    Type -> Set.empty
    Pi v _ _ t b -> fvs t <> Set.delete (Local v) (fvs b)

instance Ord v => FreeVariables1 v (Implicit v) where
  liftFvs _ = \case
    Hole v -> Set.singleton v
    Implicit -> mempty

instance (FreeVariables1 v f, FreeVariables1 v g, Ord v) => FreeVariables1 v (f :+: g) where
  liftFvs fvs = \case
    L f -> liftFvs fvs f
    R g -> liftFvs fvs g

uses :: Name -> Term (Implicit QName :+: Core Name QName) a -> [a]
uses n = cata $ \ f a -> case f of
  R (Var n')
    | Local n == n' -> [a]
    | otherwise     -> []
  R (Lam n' b)
    | n == n'   -> []
    | otherwise -> b
  R (f :$ a) -> f <> a
  R Type -> []
  R (Pi n' _ _ t b)
    | n == n'   -> t
    | otherwise -> t <> b
  L (Hole n')
    | Local n == n' -> [a]
    | otherwise     -> []
  L Implicit -> []
