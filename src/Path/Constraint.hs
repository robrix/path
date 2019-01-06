module Path.Constraint where

import Data.List.NonEmpty (NonEmpty(..), toList)
import Path.Name
import Path.Pretty
import Path.Value
import Text.Trifecta.Rendering (Span)

data Equation
  = Typed Value :===: Typed Value
  deriving (Eq, Ord, Show)

infix 1 :===:

instance Pretty Equation where
  pretty (t1 :===: t2) = flatAlt (align (space <+> pretty t1 </> pretty "≡" <+> pretty t2)) (pretty t1 <+> pretty "≡" <+> pretty t2)

instance PrettyPrec Equation

sym :: Equation -> Equation
sym (t1 :===: t2) = t2 :===: t1


data Solution
  = Meta := Typed Value
  deriving (Eq, Ord, Show)

infix 5 :=

solMeta :: Solution -> Meta
solMeta (m := _) = m

solDefn :: Solution -> Typed Value
solDefn (_ := d) = d

solValue :: Solution -> Value
solValue = typedTerm . solDefn

solType :: Solution -> Type
solType = typedType . solDefn

solBinding :: Solution -> Typed QName
solBinding (m := _ ::: t) = Meta m ::: t

instance Pretty Solution where
  pretty (m := v ::: t) = green (pretty m) <+> align (pretty "=" <+> pretty v </> colon <+> pretty t)

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
