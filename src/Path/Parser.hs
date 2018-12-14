{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Path.Parser
( Parser(..)
, parseFile
, parseString
, whole
, keyword
, identifier
, reservedWords
, op
, ErrInfo
, Span
) where

import Control.Applicative (Alternative(..))
import Control.Effect
import Control.Effect.Error
import Control.Monad (MonadPlus(..), (<=<))
import Control.Monad.IO.Class
import Control.Monad.State
import qualified Data.ByteString.Char8 as BS
import Data.Char (isSpace)
import qualified Data.HashSet as HashSet
import Text.Parser.Char
import Text.Parser.Combinators
import Text.Parser.LookAhead
import Text.Parser.Token
import Text.Parser.Token.Highlight
import Text.Parser.Token.Style
import qualified Text.Trifecta as Trifecta
import Text.Trifecta hiding (Parser, parseString, runParser)
import Text.Trifecta.Delta
import Text.Trifecta.Indentation

newtype Parser a = Parser { runParser :: StateT Int Trifecta.Parser a }
  deriving (Alternative, Applicative, CharParsing, DeltaParsing, Functor, LookAheadParsing, MarkParsing Delta, Monad, MonadPlus, Parsing)

instance TokenParsing Parser where
  someSpace = Parser $ buildSomeSpaceParser (skipSome (satisfy isSpace)) haskellCommentStyle
  nesting = Parser . nesting . runParser
  highlight h = Parser . highlight h . runParser


parseFile :: (Carrier sig m, Member (Error ErrInfo) sig, MonadIO m) => IndentationParserT Char Parser a -> FilePath -> m a
parseFile p = toError <=< parseFromFileEx (evalStateT (runParser (evalIndentationParserT p indentst)) 0)

parseString :: (Carrier sig m, Member (Error ErrInfo) sig, MonadIO m) => IndentationParserT Char Parser a -> String -> m a
parseString p = toError . Trifecta.parseString (evalStateT (runParser (evalIndentationParserT p indentst)) 0) directed

toError :: (Applicative m, Carrier sig m, Member (Error ErrInfo) sig) => Result a -> m a
toError (Success a) = pure a
toError (Failure e) = throwError e


directed :: Delta
directed = Directed BS.empty 0 0 0 0

indentst :: IndentationState
indentst = mkIndentationState 0 infIndentation True Gt

whole :: TokenParsing m => m a -> m a
whole p = whiteSpace *> p <* eof


identifier :: (Monad m, TokenParsing m) => m String
identifier = ident (IdentifierStyle "identifier" letter (alphaNum <|> char '\'') reservedWords Identifier ReservedIdentifier)

reservedWords :: HashSet.HashSet String
reservedWords =  HashSet.fromList [ "Type", "module", "where", "import" ]

keyword, op :: TokenParsing m => String -> m String

keyword s = token (highlight ReservedIdentifier (try (string s <* notFollowedBy alphaNum))) <?> s

op s = token (highlight Operator (string s)) <?> s
