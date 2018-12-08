module Path.Usage where

import Path.Semiring

data Usage
  = Zero
  | One
  | More
  deriving (Eq, Ord, Show)

instance Semigroup Usage where
  Zero <> _    = Zero
  _    <> Zero = Zero
  _    <> _    = More

instance Monoid Usage where
  mempty = Zero

instance Semiring Usage where
  Zero >< _    = Zero
  _    >< Zero = Zero
  One  >< One  = One
  _    >< _    = More
