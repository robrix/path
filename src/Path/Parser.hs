{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Path.Parser
( Parser(..)
, parseFile
, parseString
, parseError
, whole
, keyword
, identifier
, reservedWords
, op
, ErrInfo
, Delta(..)
) where

import Control.Applicative (Alternative(..))
import Control.Effect.Error
import Control.Monad (MonadPlus(..), (<=<))
import Control.Monad.IO.Class
import qualified Data.HashSet as HashSet
import Path.Pretty (Doc)
import Text.Parser.Char
import Text.Parser.Combinators
import Text.Parser.Token
import Text.Parser.Token.Highlight
import Text.Parser.Token.Style
import qualified Text.Trifecta as Trifecta
import Text.Trifecta hiding (Parser, parseString, runParser)
import Text.Trifecta.Delta

newtype Parser a = Parser { runParser :: Trifecta.Parser a }
  deriving (Alternative, Applicative, CharParsing, DeltaParsing, Functor, Monad, MonadPlus, Parsing)

instance TokenParsing Parser where
  someSpace = Parser (buildSomeSpaceParser someSpace haskellCommentStyle)
  nesting = Parser . nesting . runParser
  highlight h = Parser . highlight h . runParser
  token p = whiteSpace *> p


parseFile :: (Carrier sig m, Member (Error Doc) sig, MonadIO m) => Parser a -> FilePath -> m a
parseFile p = toError <=< parseFromFileEx (runParser p)

parseString :: (Carrier sig m, Member (Error Doc) sig) => Parser a -> Delta -> String -> m a
parseString p = fmap toError . Trifecta.parseString (runParser p)

toError :: (Carrier sig m, Member (Error Doc) sig) => Result a -> m a
toError (Success a) = pure a
toError (Failure e) = parseError e

parseError :: (Carrier sig m, Member (Error Doc) sig) => ErrInfo -> m a
parseError err = throwError (_errDoc err)


whole :: TokenParsing m => m a -> m a
whole p = p <* whiteSpace <* eof


identifier :: (Monad m, TokenParsing m) => m String
identifier = ident (IdentifierStyle "identifier" letter (alphaNum <|> char '\'') reservedWords Identifier ReservedIdentifier)


reservedWords :: HashSet.HashSet String
reservedWords = HashSet.fromList [ "Type", "module", "import" ]

keyword, op :: TokenParsing m => String -> m String

keyword s = token (highlight ReservedIdentifier (try (string s <* notFollowedBy alphaNum))) <?> s

op s = token (highlight Operator (string s)) <?> s
