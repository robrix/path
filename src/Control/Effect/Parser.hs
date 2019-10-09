{-# LANGUAGE DeriveFunctor, ExistentialQuantification, FlexibleContexts, LambdaCase, StandaloneDeriving #-}
module Control.Effect.Parser
( -- * Parser effect
  Parser(..)
, accept
, Lines(..)
, line
, position
, Path(..)
, path
, spanned
) where

import Control.Carrier
import Control.Effect.Reader
import Path.Span hiding (spanned)

data Parser m k
  = forall a . Accept (Char -> Maybe a) (a -> m k)
  | forall a . Label (m a) String (a -> m k)
  | Unexpected String
  | Position (Pos -> m k)

deriving instance Functor m => Functor (Parser m)

instance HFunctor Parser where
  hmap f = \case
    Accept p   k -> Accept p      (f . k)
    Label m s  k -> Label (f m) s (f . k)
    Unexpected s -> Unexpected s
    Position   k -> Position      (f . k)

instance Effect Parser where
  handle state handler = \case
    Accept p   k -> Accept p (handler . (<$ state) . k)
    Label m s  k -> Label (handler (m <$ state)) s (handler . fmap k)
    Unexpected s -> Unexpected s
    Position   k -> Position (handler . (<$ state) . k)


accept :: Has Parser sig m => (Char -> Maybe a) -> m a
accept p = send (Accept p pure)

newtype Lines = Lines { unLines :: [String] }

line :: (Has Parser sig m, Has (Reader Lines) sig m) => m String
line = do
  pos <- position
  asks ((!! posLine pos) . unLines)

position :: Has Parser sig m => m Pos
position = send (Position pure)

newtype Path = Path { unPath :: FilePath }

path :: Has (Reader Path) sig m => m FilePath
path = asks unPath

spanned :: (Has Parser sig m, Has (Reader Lines) sig m, Has (Reader Path) sig m) => m a -> m (Spanned a)
spanned m = do
  path <- path
  line <- line
  start <- position
  a <- m
  end <- position
  pure (a :~ Excerpt path line (Span start end))
