{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Path.Parser
( Parser(..)
, parseFile
, parseString
, whole
, keyword
, identifier
, op
, Span
) where

import Control.Applicative (Alternative(..))
import Control.Monad.IO.Class
import Control.Monad (MonadPlus(..))
import qualified Data.ByteString.Char8 as BS
import Data.Char (isSpace)
import qualified Data.HashSet as HashSet
import Text.Parser.Char
import Text.Parser.Combinators
import Text.Parser.LookAhead
import Text.Parser.Token
import Text.Parser.Token.Highlight
import Text.Parser.Token.Style
import Text.PrettyPrint.ANSI.Leijen (Doc)
import qualified Text.Trifecta as Trifecta
import Text.Trifecta hiding (Parser, parseString, runParser)
import Text.Trifecta.Delta
import Text.Trifecta.Indentation

newtype Parser a = Parser { runParser :: Trifecta.Parser a }
  deriving (Alternative, Applicative, CharParsing, DeltaParsing, Functor, LookAheadParsing, MarkParsing Delta, Monad, MonadPlus, Parsing)

instance TokenParsing Parser where
  someSpace = Parser $ buildSomeSpaceParser (skipSome (satisfy isSpace)) haskellCommentStyle
  nesting = Parser . nesting . runParser
  highlight h = Parser . highlight h . runParser


parseFile :: MonadIO m => IndentationParserT Char Parser a -> FilePath -> m (Either Doc a)
parseFile p = fmap toResult . parseFromFileEx (runParser (evalIndentationParserT p indentst))

parseString :: IndentationParserT Char Parser a -> String -> Either Doc a
parseString p = toResult . Trifecta.parseString (runParser (evalIndentationParserT p indentst)) directed

toResult :: Result a -> Either Doc a
toResult = foldResult (Left . _errDoc) Right


directed :: Delta
directed = Directed BS.empty 0 0 0 0

indentst :: IndentationState
indentst = mkIndentationState 0 infIndentation True Gt

whole :: TokenParsing m => m a -> m a
whole p = whiteSpace *> p <* eof


identifier :: (Monad m, TokenParsing m) => m String
identifier = ident (IdentifierStyle "identifier" letter (alphaNum <|> char '\'') reservedWords Identifier ReservedIdentifier) <?> "identifier"

reservedWords :: HashSet.HashSet String
reservedWords =  HashSet.fromList [ "Type", "module", "where", "import" ]

keyword, op :: TokenParsing m => String -> m String

keyword s = token (highlight ReservedIdentifier (try (string s <* notFollowedBy alphaNum))) <?> s

op s = token (highlight Operator (string s)) <?> s
