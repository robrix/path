{-# LANGUAGE DeriveFunctor, DeriveGeneric, ExistentialQuantification, FlexibleContexts, GeneralizedNewtypeDeriving, StandaloneDeriving #-}
module Path.Lexer where

import Control.Applicative (Alternative (..))
import Control.Effect.Carrier
import Control.Effect.Cut
import Control.Effect.State
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


runLexer :: Monad m => String -> LexerC m a -> m (String, Maybe a)
runLexer s = runState s . runCutAll . runLexerC

newtype LexerC m a = LexerC { runLexerC :: CutC (StateC String m) a }
  deriving (Alternative, Applicative, Functor, Monad)
