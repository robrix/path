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

data Parser m k
  = forall a . Accept (Char -> Maybe a) (a -> m k)
  | forall a . Label (m a) String (a -> m k)
  | Unexpected String
  | Eof (m k)

deriving instance Functor m => Functor (Parser m)

instance HFunctor Parser where
  hmap f (Accept p   k) = Accept p      (f . k)
  hmap f (Label m s  k) = Label (f m) s (f . k)
  hmap _ (Unexpected s) = Unexpected s
  hmap f (Eof        k) = Eof           (f   k)

instance Effect Parser where
  handle state handler (Accept p   k) = Accept p (handler . (<$ state) . k)
  handle state handler (Label m s  k) = Label (handler (m <$ state)) s (handler . fmap k)
  handle _     _       (Unexpected s) = Unexpected s
  handle state handler (Eof        k) = Eof      (handler . (<$ state) $ k)


accept :: (Carrier sig m, Member Parser sig) => (Char -> Maybe a) -> m a
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


runParser :: String -> ParserC m a -> m (String, a)
runParser s = runState s . runParserC

newtype ParserC m a = ParserC { runParserC :: StateC String m a }
  deriving (Alternative, Applicative, Functor, Monad)

instance (Alternative m, Carrier sig m, Effect sig, Member Cut sig) => Parsing (ParserC m) where
  try = call
  eof = send (Eof (pure ()))
  unexpected s = send (Unexpected s)
  m <?> s = send (Label m s pure)
  notFollowedBy m = m >>= unexpected . show

instance (Alternative m, Carrier sig m, Effect sig, Member Cut sig) => CharParsing (ParserC m) where
  satisfy p = accept (\ c -> if p c then Just c else Nothing)

instance (Alternative m, Carrier sig m, Effect sig, Member Cut sig) => TokenParsing (ParserC m)

instance (Alternative m, Carrier sig m, Effect sig) => Carrier (Parser :+: sig) (ParserC m) where
  eff = \case
    L (Accept p k) -> ParserC $ do
      cs <- get @String
      case cs of
        c:cs | Just a <- p c -> put cs *> runParserC (k a)
        -- FIXME: error message
        _                    -> empty
    -- FIXME: use the label to provide contextualized error messages
    L (Label m _ k) -> m >>= k
    -- FIXME: fail with an error message
    L (Unexpected _) -> empty
    L (Eof k) -> ParserC $ do
      cs <- get @String
      case cs of
        "" -> runParserC k
        -- FIXME: error message
        _  -> empty
    R other -> ParserC (eff (R (handleCoercible other)))
