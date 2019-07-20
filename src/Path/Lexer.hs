{-# LANGUAGE DeriveFunctor, DeriveGeneric, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, StandaloneDeriving, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.Lexer where

import           Control.Applicative (Alternative (..))
import           Control.Effect.Carrier
import           Control.Effect.Cut
import           Control.Effect.State
import qualified Data.Set as Set
import           Text.Parser.Char
import           Text.Parser.Combinators
import           Text.Parser.Token

data Lexer m k
  = forall a . Accept (Char -> Maybe a) (a -> m k)
  | forall a . Label (m a) String (a -> m k)
  | Unexpected String
  | Eof (m k)

deriving instance Functor m => Functor (Lexer m)

instance HFunctor Lexer where
  hmap f (Accept p   k) = Accept p      (f . k)
  hmap f (Label m s  k) = Label (f m) s (f . k)
  hmap _ (Unexpected s) = Unexpected s
  hmap f (Eof        k) = Eof           (f   k)

instance Effect Lexer where
  handle state handler (Accept p   k) = Accept p (handler . (<$ state) . k)
  handle state handler (Label m s  k) = Label (handler (m <$ state)) s (handler . fmap k)
  handle _     _       (Unexpected s) = Unexpected s
  handle state handler (Eof        k) = Eof      (handler . (<$ state) $ k)


accept :: (Carrier sig m, Member Lexer sig) => (Char -> Maybe a) -> m a
accept p = send (Accept p pure)


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


runLexer :: String -> LexerC m a -> m (String, a)
runLexer s = runState s . runLexerC

newtype LexerC m a = LexerC { runLexerC :: StateC String m a }
  deriving (Alternative, Applicative, Functor, Monad)

instance (Alternative m, Carrier sig m, Effect sig, Member Cut sig) => Parsing (LexerC m) where
  try = call
  eof = send (Eof (pure ()))
  unexpected s = send (Unexpected s)
  m <?> s = send (Label m s pure)
  notFollowedBy m = m >>= unexpected . show

instance (Alternative m, Carrier sig m, Effect sig, Member Cut sig) => CharParsing (LexerC m) where
  satisfy p = accept (\ c -> if p c then Just c else Nothing)

instance (Alternative m, Carrier sig m, Effect sig, Member Cut sig) => TokenParsing (LexerC m)

instance (Alternative m, Carrier sig m, Effect sig) => Carrier (Lexer :+: sig) (LexerC m) where
  eff = \case
    L (Accept p k) -> LexerC $ do
      cs <- get @String
      case cs of
        c:cs | Just a <- p c -> put cs *> runLexerC (k a)
        -- FIXME: error message
        _                    -> empty
    -- FIXME: use the label to provide contextualized error messages
    L (Label m _ k) -> m >>= k
    -- FIXME: fail with an error message
    L (Unexpected _) -> empty
    L (Eof k) -> LexerC $ do
      cs <- get @String
      case cs of
        "" -> runLexerC k
        -- FIXME: error message
        _  -> empty
    R other -> LexerC (eff (R (handleCoercible other)))
