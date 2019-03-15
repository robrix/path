{-# LANGUAGE FlexibleInstances, LambdaCase, MultiParamTypeClasses, TypeOperators #-}
module Path.Constraint where

import Data.Foldable (foldl')
import Data.List.NonEmpty (NonEmpty(..), toList)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Path.Context
import Path.Name
import Path.Pretty
import Path.Value
import Text.Trifecta.Rendering (Span, Spanned(..))

data Equation a
  = a :===: a
  deriving (Eq, Ord, Show)

infix 3 :===:

instance Pretty a => Pretty (Equation a) where
  pretty (t1 :===: t2) = flatAlt (align (space <+> pretty t1 </> eq <+> pretty t2)) (pretty t1 <+> eq <+> pretty t2)
    where eq = magenta (pretty "≡")

instance Pretty a => PrettyPrec (Equation a)

instance FreeVariables v a => FreeVariables v (Equation a) where
  fvs (a1 :===: a2) = fvs a1 <> fvs a2


type HetConstraint = Spanned (Contextual (Equation (Value Meta ::: Type Meta)))
type HomConstraint = Spanned (Contextual (Equation (Value Meta) ::: Type Meta))


data Solution
  = Gensym := Value Meta
  deriving (Eq, Ord, Show)

infix 5 :=

instance Pretty Solution where
  pretty (m := v) = green (pretty m) <+> align (pretty "=" <+> pretty v)

instance PrettyPrec Solution


data Cause
  = Assert Span
  | Via (Equation (Value Meta) ::: Type Meta) Cause
  | Cause :<>: Cause
  deriving (Eq, Ord, Show)

instance Semigroup Cause where
  (<>) = (:<>:)

spans :: Cause -> NonEmpty Span
spans = flip go []
  where go (Assert span) = (span :|)
        go (Via _ cause) = go cause
        go (l :<>: r)    = go l . toList . go r


data Caused a
  = a :@ Cause
  deriving (Eq, Ord, Show)

infix 0 :@

instance FreeVariables v a => FreeVariables v (Caused a) where
  fvs (a :@ _) = fvs a

cause :: Caused a -> Cause
cause (_ :@ cause) = cause


type Substitution = Map.Map Gensym (Value Meta)

class Substitutable t where
  apply :: [Caused Solution] -> t -> t

instance Substitutable a => Substitutable (Caused a) where
  apply subst (a :@ c) = apply subst a :@ foldl' (flip (flip (<>) . cause)) c subst

instance Substitutable (Value Meta) where
  apply []                 = id
  apply ((m := v :@ _):ss) = apply ss . substitute (Meta m) v

instance Substitutable a => Substitutable (Equation a) where
  apply subst (s1 :===: s2) = apply subst s1 :===: apply subst s2

instance (Substitutable a, Substitutable b) => Substitutable (a ::: b) where
  apply subst (tm ::: ty) = apply subst tm ::: apply subst ty

instance (Ord a, Substitutable a) => Substitutable (Set.Set a) where
  apply subst = Set.map (apply subst)

instance Substitutable a => Substitutable (Spanned a) where
  apply subst (a :~ span) = apply subst a :~ span
