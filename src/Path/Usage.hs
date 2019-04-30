module Path.Usage where

import Path.Pretty
import Path.Semiring

data Usage
  = Zero
  | One
  | More
  deriving (Eq, Ord, Show)

instance Semigroup Usage where
  Zero <> a    = a
  a    <> Zero = a
  _    <> _    = More

instance Monoid Usage where
  mempty = Zero

instance Semiring Usage where
  Zero >< _    = Zero
  _    >< Zero = Zero
  One  >< One  = One
  _    >< _    = More

instance Unital Usage where
  one = One

instance Pretty Usage where
  pretty Zero = pretty "0"
  pretty One  = pretty "1"
  pretty More = pretty "ω"
