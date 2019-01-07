{-# LANGUAGE FlexibleInstances, LambdaCase, MultiParamTypeClasses #-}
module Path.Constraint where

import Data.Foldable (foldl')
import Data.List.NonEmpty (NonEmpty(..), toList)
import Path.Name
import Path.Pretty
import Path.Value
import Text.Trifecta.Rendering (Span)

data Equation a
  = a :===: a
  deriving (Eq, Ord, Show)

infix 1 :===:

instance Pretty a => Pretty (Equation a) where
  pretty (t1 :===: t2) = flatAlt (align (space <+> pretty t1 </> pretty "≡" <+> pretty t2)) (pretty t1 <+> pretty "≡" <+> pretty t2)

instance Pretty a => PrettyPrec (Equation a)

sym :: Equation a -> Equation a
sym (t1 :===: t2) = t2 :===: t1


data Solution
  = Meta := Value
  deriving (Eq, Ord, Show)

infix 5 :=

instance Pretty Solution where
  pretty (m := v) = green (pretty m) <+> align (pretty "=" <+> pretty v)

instance PrettyPrec Solution


data Cause
  = Assert Span
  | Cause :<>: Cause
  deriving (Eq, Ord, Show)

instance Semigroup Cause where
  (<>) = (:<>:)

spans :: Cause -> NonEmpty Span
spans = flip go []
  where go (Assert span) = (span :|)
        go (l :<>: r)    = go l . toList . go r


data Caused a
  = a :@ Cause
  deriving (Eq, Ord, Show)

infix 0 :@

instance FreeVariables v a => FreeVariables v (Caused a) where
  fvs (a :@ _) = fvs a

cause :: Caused a -> Cause
cause (_ :@ cause) = cause


class Substitutable t where
  apply :: [Caused Solution] -> t -> t

instance Substitutable a => Substitutable (Caused a) where
  apply subst (a :@ c) = apply subst a :@ foldl' (flip (flip (<>) . cause)) c subst

instance Substitutable Value where
  apply []                 = id
  apply ((m := v :@ _):ss) = apply ss . subst (Meta m) v

instance Substitutable a => Substitutable (Equation a) where
  apply subst (s1 :===: s2) = apply subst s1 :===: apply subst s2

instance Substitutable a => Substitutable (Typed a) where
  apply subst (tm ::: ty) = apply subst tm ::: apply subst ty
