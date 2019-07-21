{-# LANGUAGE DeriveFunctor, DeriveGeneric, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, RankNTypes, StandaloneDeriving, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.Lexer where

import           Control.Applicative (Alternative (..))
import           Control.Effect.Carrier
import           Control.Effect.Cut
import           Control.Effect.NonDet
import           Control.Monad (MonadPlus (..), ap)
import           GHC.Generics ((:.:) (..))
import           Text.Parser.Char
import           Text.Parser.Combinators
import           Text.Parser.Token

data Parser m k
  = forall a . Accept (Char -> Maybe a) (a -> m k)
  | forall a . Label (m a) String (a -> m k)
  | Unexpected String

deriving instance Functor m => Functor (Parser m)

instance HFunctor Parser where
  hmap f (Accept p   k) = Accept p      (f . k)
  hmap f (Label m s  k) = Label (f m) s (f . k)
  hmap _ (Unexpected s) = Unexpected s

instance Effect Parser where
  handle state handler (Accept p   k) = Accept p (handler . (<$ state) . k)
  handle state handler (Label m s  k) = Label (handler (m <$ state)) s (handler . fmap k)
  handle _     _       (Unexpected s) = Unexpected s


accept :: (Carrier sig m, Member Parser sig) => (Char -> Maybe a) -> m a
accept p = send (Accept p pure)


data Pos = Pos
  { posLine   :: {-# UNPACK #-} !Int
  , posColumn :: {-# UNPACK #-} !Int
  }
  deriving (Eq, Ord, Show)

advance :: Char -> Pos -> Pos
advance '\n' p = Pos (succ (posLine p)) 0
advance _    p = p { posColumn = succ (posColumn p) }

data Span = Span
  { spanStart :: {-# UNPACK #-} !Pos
  , spanEnd   :: {-# UNPACK #-} !Pos
  }
  deriving (Eq, Ord, Show)


runParser :: Applicative m => Pos -> String -> ParserC m a -> m (Either Err (String, a))
runParser p s m = runParserC m (const (curry (pure . Right))) (pure . Left) (pure . Left) p s

newtype ParserC m a = ParserC
  { runParserC
    :: forall r
    .  (Pos -> String -> a -> m r) -- success
    -> (Err -> m r)                -- empty
    -> (Err -> m r)                -- cut
    -> Pos
    -> String
    -> m r
  }
  deriving (Functor)

instance Applicative (ParserC m) where
  pure a = ParserC (\ just _ _ pos input -> just pos input a)
  (<*>) = ap

instance Alternative (ParserC m) where
  empty = ParserC (\ _ nothing _ pos _ -> nothing (Err pos ""))

  ParserC l <|> ParserC r = ParserC (\ just nothing fail pos input -> l just (const (r just nothing fail pos input)) fail pos input)

instance Monad (ParserC m) where
  m >>= f = ParserC (\ just nothing fail pos input -> runParserC m (\ pos input a -> runParserC (f a) just nothing fail pos input) nothing fail pos input)

instance MonadPlus (ParserC m)

instance (Carrier sig m, Effect sig) => Parsing (ParserC m) where
  try = call
  eof = notFollowedBy anyChar <?> "end of input"
  unexpected s = send (Unexpected s)
  m <?> s = send (Label m s pure)
  notFollowedBy p = try (optional p >>= maybe (pure ()) (unexpected . show))

instance (Carrier sig m, Effect sig) => CharParsing (ParserC m) where
  satisfy p = accept (\ c -> if p c then Just c else Nothing)

instance (Carrier sig m, Effect sig) => TokenParsing (ParserC m)

instance (Carrier sig m, Effect sig) => Carrier (Parser :+: Cut :+: NonDet :+: sig) (ParserC m) where
  eff = \case
    L (Accept p k) -> ParserC (\ just nothing _ pos -> \case
      c:cs | Just a <- p c -> just (advance c pos) cs a
           | otherwise     -> nothing (Err pos ("unexpected " ++ show c))
      _                    -> nothing (Err pos "unexpected EOF")) >>= k
    L (Label m s k) -> ParserC (\ just nothing fail -> runParserC m just (nothing . setErrReason s) (fail . setErrReason s)) >>= k
    L (Unexpected s) -> ParserC $ \ _ nothing _ pos _ -> nothing (Err pos s)
    R (L Cutfail) -> ParserC $ \ _ _ fail pos _ -> fail (Err pos "")
    R (L (Call m k)) -> ParserC (\ just nothing _ -> runParserC m just nothing nothing) >>= k
    R (R (L Empty)) -> empty
    R (R (L (Choose k))) -> k True <|> k False
    R (R (R other)) -> ParserC $ \ just nothing _ pos input -> eff (handle (Comp1 (Right (input, ()))) (either (pure . Comp1 . Left) (fmap Comp1 . uncurry (runParser pos)) . unComp1) other) >>= either nothing (uncurry (just pos)) . unComp1


data Err = Err
  { errPos    :: {-# UNPACK #-} !Pos
  , errReason :: String
  }
  deriving (Eq, Ord, Show)

setErrReason :: String -> Err -> Err
setErrReason s e = e { errReason = if null (errReason e) then s else errReason e }
