{-# LANGUAGE DeriveTraversable, FlexibleContexts #-}
module Path.Span
( Span(..)
, Pos(..)
, advancePos
, Excerpt(..)
, excerptHere
, Spanned(..)
, unSpanned
, runSpanned
, runInContext
, spanned
, spanIs
) where

import Control.Carrier.Reader
import Data.Maybe (listToMaybe)
import GHC.Stack

data Span = Span
  { spanStart :: {-# UNPACK #-} !Pos
  , spanEnd   :: {-# UNPACK #-} !Pos
  }
  deriving (Eq, Ord, Show)

instance Semigroup Span where
  Span s1 e1 <> Span s2 e2 = Span (min s1 s2) (max e1 e2)


data Pos = Pos
  { posLine   :: {-# UNPACK #-} !Int
  , posColumn :: {-# UNPACK #-} !Int
  }
  deriving (Eq, Ord, Show)

advancePos :: Char -> Pos -> Pos
advancePos '\n' p = Pos (succ (posLine p)) 0
advancePos _    p = p { posColumn = succ (posColumn p) }


data Excerpt = Excerpt
  { excerptPath :: FilePath
  , excerptLine :: String
  , excerptSpan :: {-# UNPACK #-} !Span
  }
  deriving (Eq, Ord, Show)

instance Semigroup Excerpt where
  Excerpt _ l s1 <> Excerpt p _ s2 = Excerpt p l (s1 <> s2)

excerptHere :: HasCallStack => Excerpt
excerptHere = maybe (Excerpt "(unknown)" "" (Span (Pos 0 0) (Pos 0 0))) (mk . snd) (listToMaybe (getCallStack callStack))
  where mk s = Excerpt (srcLocFile s) "" (Span (Pos (pred (srcLocStartLine s)) (pred (srcLocStartCol s))) (Pos (pred (srcLocEndLine s)) (pred (srcLocEndCol s))))


data Spanned a = a :~ Excerpt
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

unSpanned :: Spanned a -> a
unSpanned (a :~ _) = a


runSpanned :: Carrier sig m => (a -> ReaderC Excerpt m b) -> Spanned a -> m (Spanned b)
runSpanned f v@(_ :~ s) = runReader s (traverse f v)

runInContext :: Carrier sig m => (a -> ReaderC c m b) -> (c, a) -> m (c, b)
runInContext f v = runReader (fst v) (traverse f v)

spanned :: Has (Reader Excerpt) sig m => a -> m (Spanned a)
spanned a = asks (a :~)

spanIs :: Has (Reader Excerpt) sig m => Spanned (m a) -> m a
spanIs (m :~ s) = local (const s) m
