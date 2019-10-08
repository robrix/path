{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, RankNTypes, TypeOperators, UndecidableInstances #-}
module Control.Carrier.Parser.Church
( -- * Parser effect
  module Control.Effect.Parser
  -- * Parsr carrier
, parseString
, parseFile
, runParser
, ParserC(..)
) where

import Control.Applicative (Alternative(..))
import Control.Effect.Carrier
import Control.Effect.Cut
import Control.Effect.Error
import Control.Effect.NonDet
import Control.Effect.Parser
import Control.Effect.Reader
import Control.Monad (MonadPlus, ap)
import Control.Monad.IO.Class
import Data.Maybe (fromMaybe)
import Path.Error (Level(..), Notice(..))
import Path.Pretty (Doc, pretty)
import Path.Span
import Text.Parser.Char
import Text.Parser.Combinators
import Text.Parser.Token

parseString :: (Carrier sig m, Member (Error Notice) sig) => ParserC (ReaderC FilePath (ReaderC [String] m)) a -> Pos -> String -> m a
parseString p pos input = runParser "(interactive)" pos input p >>= either throwError pure

parseFile :: (Carrier sig m, Member (Error Notice) sig, MonadIO m) => ParserC (ReaderC FilePath (ReaderC [String] m)) a -> FilePath -> m a
parseFile p path = do
  input <- liftIO (readFile path)
  runParser path (Pos 0 0) input p >>= either throwError pure

runParser :: Applicative m => FilePath -> Pos -> String -> ParserC (ReaderC FilePath (ReaderC [String] m)) a -> m (Either Notice a)
runParser path pos input m = runReader inputLines (runReader path (runParserC m success failure failure pos input)) where
  success _ _ a = pure (Right a)
  failure pos reason = pure (Left (Notice (Just Error) (Excerpt path (inputLines !! posLine pos) (Span pos pos)) (fromMaybe (pretty "unknown error") reason) []))
  inputLines = lines input
  lines "" = [""]
  lines s  = let (line, rest) = takeLine s in line : lines rest
  takeLine ""          = ("", "")
  takeLine ('\n':rest) = ("\n", rest)
  takeLine (c   :rest) = let (cs, rest') = takeLine rest in (c:cs, rest')

newtype ParserC m a = ParserC
  { runParserC
    :: forall r
    .  (Pos -> String -> a -> m r) -- success
    -> (Pos -> Maybe Doc -> m r)   -- empty
    -> (Pos -> Maybe Doc -> m r)   -- cut
    -> Pos
    -> String
    -> m r
  }
  deriving (Functor)

instance Applicative (ParserC m) where
  pure a = ParserC (\ just _ _ pos input -> just pos input a)
  (<*>) = ap

instance Alternative (ParserC m) where
  empty = ParserC (\ _ nothing _ pos _ -> nothing pos Nothing)

  ParserC l <|> ParserC r = ParserC (\ just nothing fail pos input -> l just (const (const (r just nothing fail pos input))) fail pos input)

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
             | otherwise     -> nothing pos (Just (pretty "unexpected " <> pretty c))
        _                    -> nothing pos (Just (pretty "unexpected EOF"))) >>= k
      Label m s k -> ParserC (\ just nothing fail -> runParserC m just (\ p r -> nothing p (r <|> Just (pretty s))) (\ p r -> fail p (r <|> Just (pretty s)))) >>= k
      Unexpected s -> ParserC $ \ _ nothing _ pos _ -> nothing pos (Just (pretty s))
      Position k -> ParserC (\ just _ _ pos input -> just pos input pos) >>= k
    R (L cut) -> case cut of
      Cutfail -> ParserC $ \ _ _ fail pos _ -> fail pos Nothing
      Call m k -> ParserC (\ just nothing _ -> runParserC m just nothing nothing) >>= k
    R (R (L nondet)) -> case nondet of
      Empty -> empty
      Choose k -> k True <|> k False
    R (R (R other)) -> ParserC $ \ just nothing _ pos input -> eff (handle (success pos input ()) (result runParser failure) other) >>= result just nothing where
      runParser p s m = runParserC m (\ p s -> pure . success p s) failure failure p s
      success pos input a = Result pos (Right (input, a))
      failure pos reason = pure (Result pos (Left reason))


data Result a = Result
  { resultPos   :: {-# UNPACK #-} !Pos
  , resultState :: Either (Maybe Doc) (String, a)
  }
  deriving (Foldable, Functor, Show, Traversable)

result :: (Pos -> String -> a -> b) -> (Pos -> Maybe Doc -> b) -> Result a -> b
result success failure (Result pos state) = either (failure pos) (uncurry (success pos)) state
