{-# LANGUAGE DeriveGeneric, DeriveTraversable, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MultiParamTypeClasses, RankNTypes, StandaloneDeriving, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.Lexer where

import Control.Applicative (Alternative (..))
import Control.Effect.Carrier
import Control.Effect.Cut
import Control.Effect.Error
import Control.Effect.NonDet
import Control.Monad (MonadPlus (..), ap)
import Control.Monad.IO.Class
import Data.Foldable (fold)
import Data.List (isSuffixOf)
import Path.Pretty as Pretty
import Text.Parser.Char
import Text.Parser.Combinators
import Text.Parser.Token

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

position :: (Carrier sig m, Member Parser sig) => m Pos
position = send (Position pure)

spanned :: (Carrier sig m, Member Parser sig) => m a -> m (Spanned a)
spanned m = do
  start <- position
  a <- m
  end <- position
  pure (a :~ Span start end)


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

data Spanned a = a :~ Span
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

unSpanned :: Spanned a -> a
unSpanned (a :~ _) = a


runParser :: Applicative m => FilePath -> Pos -> String -> ParserC m a -> m (Either Err a)
runParser path pos input m = runParserC m success failure failure pos input
  where success _ _ = pure . Right
        failure = pure . Left . Err path input

parseString :: (Carrier sig m, Member (Error Doc) sig) => ParserC m a -> Pos -> String -> m a
parseString p pos input = runParser "(interactive)" pos input p >>= either (throwError . pretty) pure

parseFile :: (Carrier sig m, Member (Error Doc) sig, MonadIO m) => ParserC m a -> FilePath -> m a
parseFile p path = do
  input <- liftIO (readFile path)
  runParser path (Pos 1 1) input p >>= either (throwError . pretty) pure

newtype ParserC m a = ParserC
  { runParserC
    :: forall r
    .  (Pos -> String -> a -> m r) -- success
    -> (Fail -> m r)               -- empty
    -> (Fail -> m r)               -- cut
    -> Pos
    -> String
    -> m r
  }
  deriving (Functor)

instance Applicative (ParserC m) where
  pure a = ParserC (\ just _ _ pos input -> just pos input a)
  (<*>) = ap

instance Alternative (ParserC m) where
  empty = ParserC (\ _ nothing _ pos _ -> nothing (Fail pos Nothing))

  ParserC l <|> ParserC r = ParserC (\ just nothing fail pos input -> l just (const (r just nothing fail pos input)) fail pos input)

instance Monad (ParserC m) where
  m >>= f = ParserC (\ just nothing fail -> runParserC m (\ pos input a -> runParserC (f a) just nothing fail pos input) nothing fail)

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
      Accept p k -> ParserC (\ just nothing _ pos input -> case input of
        c:cs | Just a <- p c -> just (advancePos c pos) cs a
             | otherwise     -> nothing (Fail pos (Just (pretty "unexpected " <> pretty c)))
        _                    -> nothing (Fail pos (Just (pretty "unexpected EOF")))) >>= k
      Label m s k -> ParserC (\ just nothing fail -> runParserC m just (nothing . setFailReason (pretty s)) (fail . setFailReason (pretty s))) >>= k
      Unexpected s -> ParserC $ \ _ nothing _ pos _ -> nothing (Fail pos (Just (pretty s)))
      Position k -> ParserC (\ just _ _ pos input -> just pos input pos) >>= k
    R (L cut) -> case cut of
      Cutfail -> ParserC $ \ _ _ fail pos _ -> fail (Fail pos Nothing)
      Call m k -> ParserC (\ just nothing _ -> runParserC m just nothing nothing) >>= k
    R (R (L nondet)) -> case nondet of
      Empty -> empty
      Choose k -> k True <|> k False
    R (R (R other)) -> ParserC $ \ just nothing _ pos input -> eff (handle (Success pos input ()) (result runParser (pure . Failure)) other) >>= result just nothing
    where runParser p s m = runParserC m (\ p s -> pure . Success p s) (pure . Failure) (pure . Failure) p s


data Fail = Fail
  { failPos    :: {-# UNPACK #-} !Pos
  , failReason :: Maybe Doc
  }
  deriving (Show)

setFailReason :: Doc -> Fail -> Fail
setFailReason s e = e { failReason = failReason e <|> Just s }


data Err = Err
  { errPath    :: !FilePath
  , errSource  :: !String
  , errFailure :: {-# UNPACK #-} !Fail
  }
  deriving (Show)

instance Pretty Err where
  pretty (Err path text (Fail pos reason))
    =  bold (pretty path) <> colon <> pretty pos <> colon <+> red (pretty "error") <> colon <+> pretty reason <> hardline
    <> blue (pretty (posLine pos)) <+> align (fold
      [ blue (pretty '|') <+> excerpt pos
      , blue (pretty '|') <+> caret pos
      ])
    where excerpt pos = let e = lines text !! pred (posLine pos) in pretty e <> if "\n" `isSuffixOf` e then mempty else blue (pretty "<EOF>") <> hardline
          caret pos = pretty (replicate (posColumn pos) ' ') <> green (pretty '^')
          colon = Pretty.colon
          lines "" = [""]
          lines s  = let (line, rest) = takeLine s in line : lines rest
          takeLine ""          = ("", "")
          takeLine ('\n':rest) = ("\n", rest)
          takeLine (c   :rest) = let (cs, rest') = takeLine rest in (c:cs, rest')


data Result a
  = Success Pos String a
  | Failure Fail
  deriving (Foldable, Functor, Show, Traversable)

result :: (Pos -> String -> a -> b) -> (Fail -> b) -> Result a -> b
result success failure = \case
  Success p s a -> success p s a
  Failure e     -> failure e
