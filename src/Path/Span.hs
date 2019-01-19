module Path.Span where

data Pos = Pos
  { posLine :: {-# UNPACK #-} !Int
  , posCol  :: {-# UNPACK #-} !Int
  }
  deriving (Eq, Ord, Show)
