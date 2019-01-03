module Path.Type where

import Path.Pretty
import Path.Value

type Type = Value

data Typed a = a ::: Type
  deriving (Eq, Ord, Show)

typedTerm :: Typed a -> a
typedTerm (a ::: _) = a

typedType :: Typed a -> Type
typedType (_ ::: t) = t

infix 6 :::

instance Pretty a => Pretty (Typed a) where
  pretty (a ::: t) = pretty a <+> colon <+> pretty t

instance Pretty a => PrettyPrec (Typed a)


data Equation
  = Typed Value :===: Typed Value
  deriving (Eq, Ord, Show)

infix 1 :===:

instance Pretty Equation where
  pretty (t1 :===: t2) = flatAlt (align (space <+> pretty t1 </> pretty "≡" <+> pretty t2)) (pretty t1 <+> pretty "≡" <+> pretty t2)

instance PrettyPrec Equation

sym :: Equation -> Equation
sym (t1 :===: t2) = t2 :===: t1
