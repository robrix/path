{-# LANGUAGE DeriveFunctor, DeriveGeneric, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, StandaloneDeriving, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.Lexer where

import Control.Applicative (Alternative (..))
import Control.Effect.Carrier
import Control.Effect.State
import Data.Char (isSpace)
import Data.Foldable (traverse_)

data Lexer m k
  = forall a . Accept (Char -> Maybe a) (a -> m k)
  | forall a . Label (m a) String (a -> m k)
  | Eof (m k)

deriving instance Functor m => Functor (Lexer m)

instance HFunctor Lexer where
  hmap f (Accept p  k) = Accept p      (f . k)
  hmap f (Label m s k) = Label (f m) s (f . k)
  hmap f (Eof       k) = Eof           (f   k)

instance Effect Lexer where
  handle state handler (Accept p  k) = Accept p (handler . (<$ state) . k)
  handle state handler (Label m s k) = Label (handler (m <$ state)) s (handler . fmap k)
  handle state handler (Eof       k) = Eof      (handler . (<$ state) $ k)


accept :: (Carrier sig m, Member Lexer sig) => (Char -> Maybe a) -> m a
accept p = send (Accept p pure)

satisfy :: (Carrier sig m, Member Lexer sig) => (Char -> Bool) -> m Char
satisfy p = accept (\ c -> if p c then Just c else Nothing)

char :: (Carrier sig m, Member Lexer sig) => Char -> m Char
char c = satisfy (c ==) <?> show [c]

string :: (Carrier sig m, Member Lexer sig) => String -> m String
string s = s <$ traverse_ char s <?> show s


skipMany :: Alternative m => m a -> m ()
skipMany p = () <$ many p

skipSome :: Alternative m => m a -> m ()
skipSome p = p *> skipMany p


someSpace :: (Alternative m, Carrier sig m, Member Lexer sig) => m ()
someSpace = skipSome (satisfy isSpace)

token :: (Alternative m, Carrier sig m, Member Lexer sig) => m a -> m a
token p = p <* (someSpace <|> pure ())


(<?>) :: (Carrier sig m, Member Lexer sig) => m a -> String -> m a
m <?> s = send (Label m s pure)

infixr 0 <?>


eof :: (Carrier sig m, Member Lexer sig) => m ()
eof = send (Eof (pure ()))


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
    L (Eof k) -> LexerC $ do
      cs <- get @String
      case cs of
        "" -> runLexerC k
        -- FIXME: error message
        _  -> empty
    R other -> LexerC (eff (R (handleCoercible other)))
