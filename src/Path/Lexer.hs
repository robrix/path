{-# LANGUAGE DeriveGeneric, DeriveTraversable, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, RankNTypes, StandaloneDeriving, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.Lexer where

import           Control.Applicative (Alternative (..))
import           Control.Effect.Carrier
import           Control.Effect.Cut
import           Control.Effect.Error
import           Control.Effect.NonDet
import           Control.Monad (MonadPlus (..), ap)
import           Data.Foldable (fold)
import           Data.List (isSuffixOf)
import           Path.Pretty as Pretty
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

instance Pretty Pos where
  pretty (Pos l c) = bold (pretty l) <> Pretty.colon <> bold (pretty c)

advancePos :: Char -> Pos -> Pos
advancePos '\n' p = Pos (succ (posLine p)) 0
advancePos _    p = p { posColumn = succ (posColumn p) }

data Span = Span
  { spanStart :: {-# UNPACK #-} !Pos
  , spanEnd   :: {-# UNPACK #-} !Pos
  }
  deriving (Eq, Ord, Show)


runParser :: Applicative m => ParserState -> ParserC m a -> m (Result a)
runParser s m = runParserC m (\ s -> pure . Success s) (pure . Failure) (pure . Failure) s

parseString :: (Carrier sig m, Member (Error Doc) sig) => ParserC m a -> Pos -> String -> m a
parseString p pos input = runParser (ParserState pos input) p >>= toError "(interactive)" input

newtype ParserC m a = ParserC
  { runParserC
    :: forall r
    .  (ParserState -> a -> m r) -- success
    -> (Err -> m r)              -- empty
    -> (Err -> m r)              -- cut
    -> ParserState
    -> m r
  }
  deriving (Functor)

instance Applicative (ParserC m) where
  pure a = ParserC (\ just _ _ state -> just state a)
  (<*>) = ap

instance Alternative (ParserC m) where
  empty = ParserC (\ _ nothing _ state -> nothing (Err (statePos state) ""))

  ParserC l <|> ParserC r = ParserC (\ just nothing fail state -> l just (const (r just nothing fail state)) fail state)

instance Monad (ParserC m) where
  m >>= f = ParserC (\ just nothing fail -> runParserC m (\ state a -> runParserC (f a) just nothing fail state) nothing fail)

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
    L parser -> case parser of
      Accept p k -> ParserC (\ just nothing _ state -> case stateInput state of
        c:_ | Just a <- p c -> just (advanceState c state) a
            | otherwise     -> nothing (Err (statePos state) ("unexpected " ++ show c))
        _                   -> nothing (Err (statePos state) "unexpected EOF")) >>= k
      Label m s k -> ParserC (\ just nothing fail -> runParserC m just (nothing . setErrReason s) (fail . setErrReason s)) >>= k
      Unexpected s -> ParserC $ \ _ nothing _ state -> nothing (Err (statePos state) s)
    R (L cut) -> case cut of
      Cutfail -> ParserC $ \ _ _ fail state -> fail (Err (statePos state) "")
      Call m k -> ParserC (\ just nothing _ -> runParserC m just nothing nothing) >>= k
    R (R (L nondet)) -> case nondet of
      Empty -> empty
      Choose k -> k True <|> k False
    R (R (R other)) -> ParserC $ \ just nothing _ state -> eff (handle (Success state ()) (result runParser (pure . Failure)) other) >>= result just nothing


data Err = Err
  { errPos    :: {-# UNPACK #-} !Pos
  , errReason :: String
  }
  deriving (Eq, Ord, Show)

setErrReason :: String -> Err -> Err
setErrReason s e = e { errReason = if null (errReason e) then s else errReason e }


data Result a
  = Success ParserState a
  | Failure Err
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

result :: (ParserState -> a -> b) -> (Err -> b) -> Result a -> b
result success failure = \case
  Success s a -> success s a
  Failure e   -> failure e

toError :: (Carrier sig m, Member (Error Doc) sig) => FilePath -> String -> Result a -> m a
toError path text = result (const pure) (throwError . prettyErr)
  where prettyErr (Err pos reason)
          =  bold (pretty path) <> colon <> pretty pos <> colon <+> red (pretty "error") <> colon <+> pretty reason <> hardline
          <> blue (pretty (posLine pos)) <+> align (fold
            [ blue (pretty '|') <+> excerpt pos
            , blue (pretty '|') <+> caret pos
            ])
        excerpt pos = let e = lines text !! pred (posLine pos) in pretty e <> if "\n" `isSuffixOf` e then mempty else blue (pretty "<EOF>") <> hardline
        caret pos = pretty (replicate (posColumn pos) ' ') <> green (pretty '^')
        colon = Pretty.colon
        lines "" = [""]
        lines s  = let (line, rest) = takeLine s in line : lines rest
        takeLine ""          = ("", "")
        takeLine ('\n':rest) = ("\n", rest)
        takeLine (c   :rest) = let (cs, rest') = takeLine rest in (c:cs, rest')


data ParserState = ParserState
  { statePos   :: {-# UNPACK #-} !Pos
  , stateInput :: !String
  }
  deriving (Eq, Ord, Show)

advanceState :: Char -> ParserState -> ParserState
advanceState c s = ParserState (advancePos c (statePos s)) (drop 1 (stateInput s))
