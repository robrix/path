{-# LANGUAGE DeriveFunctor, ExistentialQuantification, FlexibleContexts, StandaloneDeriving #-}
module Control.Effect.Parser
( -- * Parser effect
  Parser(..)
, accept
, line
, position
, path
, spanned
) where

import Control.Effect.Carrier
import Control.Effect.Reader
import Path.Span hiding (spanned)

data Parser m k
  = forall a . Accept (Char -> Maybe a) (a -> m k)
  | forall a . Label (m a) String (a -> m k)
  | Unexpected String
  | Position (Pos -> m k)

deriving instance Functor m => Functor (Parser m)

instance HFunctor Parser where
  hmap f (Accept p   k) = Accept p      (f . k)
  hmap f (Label m s  k) = Label (f m) s (f . k)
  hmap _ (Unexpected s) = Unexpected s
  hmap f (Position   k) = Position      (f . k)

instance Effect Parser where
  handle state handler (Accept p   k) = Accept p (handler . (<$ state) . k)
  handle state handler (Label m s  k) = Label (handler (m <$ state)) s (handler . fmap k)
  handle _     _       (Unexpected s) = Unexpected s
  handle state handler (Position   k) = Position (handler . (<$ state) . k)


accept :: (Carrier sig m, Member Parser sig) => (Char -> Maybe a) -> m a
accept p = send (Accept p pure)

line :: (Carrier sig m, Member Parser sig, Member (Reader [String]) sig) => m String
line = do
  pos <- position
  asks (!! posLine pos)

position :: (Carrier sig m, Member Parser sig) => m Pos
position = send (Position pure)

path :: (Carrier sig m, Member (Reader FilePath) sig) => m FilePath
path = ask

spanned :: (Carrier sig m, Member (Reader [String]) sig, Member (Reader FilePath) sig, Member Parser sig) => m a -> m (Spanned a)
spanned m = do
  path <- path
  line <- line
  start <- position
  a <- m
  end <- position
  pure (a :~ Excerpt path line (Span start end))
