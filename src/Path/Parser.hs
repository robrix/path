{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Path.Parser
( Parser
, Inner(..)
, parseFile
, parseString
, parseError
, whole
, keyword
, identifier
, reservedWords
, op
, ErrInfo
, Span(..)
, Delta(..)
) where

import Control.Applicative (Alternative(..))
import Control.Effect
import Control.Effect.Error
import Control.Monad (MonadPlus(..), (<=<))
import Control.Monad.IO.Class
import qualified Data.HashSet as HashSet
import Path.Pretty (Doc)
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

type Parser = IndentationParserT Token Inner

newtype Inner a = Inner { runInner :: Trifecta.Parser a }
  deriving (Alternative, Applicative, CharParsing, DeltaParsing, Functor, LookAheadParsing, MarkParsing Delta, Monad, MonadPlus, Parsing)

instance TokenParsing Inner where
  someSpace = Inner (buildSomeSpaceParser someSpace haskellCommentStyle)
  nesting = Inner . nesting . runInner
  highlight h = Inner . highlight h . runInner
  token p = whiteSpace *> p


parseFile :: (Carrier sig m, Member (Error Doc) sig, MonadIO m) => Parser a -> FilePath -> m a
parseFile p = toError <=< parseFromFileEx (runInner (evalIndentationParserT p indentst))

parseString :: (Carrier sig m, Member (Error Doc) sig) => Parser a -> Delta -> String -> m a
parseString p = fmap toError . Trifecta.parseString (runInner (evalIndentationParserT p indentst))

toError :: (Carrier sig m, Member (Error Doc) sig) => Result a -> m a
toError (Success a) = pure a
toError (Failure e) = parseError e

parseError :: (Carrier sig m, Member (Error Doc) sig) => ErrInfo -> m a
parseError err = throwError (_errDoc err)


indentst :: IndentationState
indentst = mkIndentationState 0 infIndentation True Gt

whole :: TokenParsing m => m a -> m a
whole p = p <* whiteSpace <* eof


identifier :: (Monad m, TokenParsing m) => m String
identifier = ident (IdentifierStyle "identifier" letter (alphaNum <|> char '\'') reservedWords Identifier ReservedIdentifier)


reservedWords :: HashSet.HashSet String
reservedWords = HashSet.fromList [ "Type", "module", "import" ]

keyword, op :: TokenParsing m => String -> m String

keyword s = token (highlight ReservedIdentifier (try (string s <* notFollowedBy alphaNum))) <?> s

op s = token (highlight Operator (string s)) <?> s
