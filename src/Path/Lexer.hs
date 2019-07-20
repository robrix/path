{-# LANGUAGE DeriveFunctor, DeriveGeneric, FlexibleContexts #-}
module Path.Lexer where

import Control.Effect.Carrier
import GHC.Generics (Generic1)

data Lexer m k
  = Satisfy (Char -> Bool) (Char -> m k)
  deriving (Functor, Generic1)

instance HFunctor Lexer
instance Effect Lexer


satisfy :: (Carrier sig m, Member Lexer sig) => (Char -> Bool) -> m Char
satisfy p = send (Satisfy p pure)


data Pos = Pos
  { posLine   :: {-# UNPACK #-} !Int
  , posColumn :: {-# UNPACK #-} !Int
  }
  deriving (Eq, Ord, Show)

data Span = Span
  { spanStart :: {-# UNPACK #-} !Int
  , spanEnd   :: {-# UNPACK #-} !Int
  }
  deriving (Eq, Ord, Show)
