module Path.Span where

import qualified Data.ByteString.Char8 as Char8
import qualified Text.Trifecta.Delta as Trifecta
import qualified Text.Trifecta.Rendering as Trifecta

data Pos = Pos
  { posLine :: {-# UNPACK #-} !Int
  , posCol  :: {-# UNPACK #-} !Int
  }
  deriving (Eq, Ord, Show)

fromDelta :: Trifecta.Delta -> Pos
fromDelta d = Pos (fromIntegral (line d)) (fromIntegral (Trifecta.column d))
  where line (Trifecta.Lines      l _ _ _) = l
        line (Trifecta.Directed _ l _ _ _) = l
        line _                             = 1

toDelta :: Maybe FilePath -> Pos -> Trifecta.Delta
toDelta Nothing  (Pos l c) = Trifecta.Lines (fromIntegral l) (fromIntegral c) 0 (fromIntegral c)
toDelta (Just p) (Pos l c) = Trifecta.Directed (Char8.pack p) (fromIntegral l) (fromIntegral c) 0 (fromIntegral c)

data Span = Span
  { spanStart :: {-# UNPACK #-} !Pos
  , spanEnd   :: {-# UNPACK #-} !Pos
  }
  deriving (Eq, Ord, Show)

instance Semigroup Span where
  Span start1 end1 <> Span start2 end2 = Span (min start1 start2) (max end1 end2)

fromSpan :: Trifecta.Span -> Span
fromSpan (Trifecta.Span d1 d2 _) = Span (fromDelta d1) (fromDelta d2)
