{-# LANGUAGE DeriveFunctor, DeriveGeneric, ExistentialQuantification, FlexibleContexts, StandaloneDeriving #-}
module Path.Lexer where

import Control.Effect.Carrier

data Lexer m k
  = forall a . Accept (Char -> Maybe a) (a -> m k)

deriving instance Functor m => Functor (Lexer m)

instance HFunctor Lexer where
  hmap f (Accept p k) = Accept p (f . k)

instance Effect Lexer where
  handle state handler (Accept p k) = Accept p (handler . (<$ state) . k)


accept :: (Carrier sig m, Member Lexer sig) => (Char -> Maybe a) -> m a
accept p = send (Accept p pure)

satisfy :: (Carrier sig m, Member Lexer sig) => (Char -> Bool) -> m Char
satisfy p = accept (\ c -> if p c then Just c else Nothing)


data Pos = Pos
  { posLine   :: {-# UNPACK #-} !Int
  , posColumn :: {-# UNPACK #-} !Int
  }
  deriving (Eq, Ord, Show)

data Span = Span
  { spanStart :: {-# UNPACK #-} !Pos
  , spanEnd   :: {-# UNPACK #-} !Pos
  }
  deriving (Eq, Ord, Show)
