{-# LANGUAGE DeriveTraversable, FlexibleContexts #-}
module Path.Span
( Span(..)
, Pos(..)
, advancePos
, Excerpt(..)
, excerpt
, Spanned(..)
, unSpanned
, runSpanned
, runInContext
, spanned
, spanIs
) where

import Control.Effect.Reader
import Text.PrettyPrint.ANSI.Leijen

data Span = Span
  { spanStart :: {-# UNPACK #-} !Pos
  , spanEnd   :: {-# UNPACK #-} !Pos
  }
  deriving (Eq, Ord, Show)

instance Semigroup Span where
  Span s1 e1 <> Span s2 e2 = Span (min s1 s2) (max e1 e2)

instance Pretty Span where
  pretty (Span start end)
    | start == end                 = green (pretty '^')
    | posLine start == posLine end = green (pretty (replicate (posColumn end - posColumn start) '~'))
    | otherwise                    = green (pretty "^…")


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

excerpt :: FilePath -> String -> Span -> Excerpt
excerpt path text span = Excerpt path (lines text !! pred (posLine (spanStart span))) span
  where lines "" = [""]
        lines s  = let (line, rest) = takeLine s in line : lines rest
        takeLine ""          = ("", "")
        takeLine ('\n':rest) = ("\n", rest)
        takeLine (c   :rest) = let (cs, rest') = takeLine rest in (c:cs, rest')


data Spanned a = a :~ Excerpt
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

unSpanned :: Spanned a -> a
unSpanned (a :~ _) = a


runSpanned :: Carrier sig m => (a -> ReaderC Excerpt m b) -> Spanned a -> m (Spanned b)
runSpanned f v@(_ :~ s) = runReader s (traverse f v)

runInContext :: Carrier sig m => (a -> ReaderC c m b) -> (c, a) -> m (c, b)
runInContext f v = runReader (fst v) (traverse f v)

spanned :: (Carrier sig m, Member (Reader Excerpt) sig) => a -> m (Spanned a)
spanned a = asks (a :~)

spanIs :: (Carrier sig m, Member (Reader Excerpt) sig) => Spanned (m a) -> m a
spanIs (m :~ s) = local (const s) m
