module Path.Span where

data Pos = Pos
  { posLine :: {-# UNPACK #-} !Int
  , posCol  :: {-# UNPACK #-} !Int
  }
  deriving (Eq, Ord, Show)

data Span = Span
  { spanStart :: {-# UNPACK #-} !Pos
  , spanEnd   :: {-# UNPACK #-} !Pos
  }
  deriving (Eq, Ord, Show)
