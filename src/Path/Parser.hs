{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Path.Parser
( Parser
, Inner(..)
, parseFile
, parseString
, whole
, keyword
, identifier
, operator
, reservedWords
, reservedOperators
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
import Control.Monad.State
import Data.Char (isPunctuation, isSymbol)
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

type Parser = IndentationParserT Token Inner

newtype Inner a = Inner { runInner :: StateT Int Trifecta.Parser a }
  deriving (Alternative, Applicative, CharParsing, DeltaParsing, Functor, LookAheadParsing, MarkParsing Delta, Monad, MonadPlus, Parsing)

instance TokenParsing Inner where
  someSpace = Inner (buildSomeSpaceParser someSpace haskellCommentStyle)
  nesting = Inner . nesting . runInner
  highlight h = Inner . highlight h . runInner
  token p = whiteSpace *> p


parseFile :: (Carrier sig m, Member (Error ErrInfo) sig, MonadIO m) => Parser a -> FilePath -> m a
parseFile p = toError <=< parseFromFileEx (evalStateT (runInner (evalIndentationParserT p indentst)) 0)

parseString :: (Carrier sig m, Member (Error ErrInfo) sig, MonadIO m) => Parser a -> Delta -> String -> m a
parseString p = fmap toError . Trifecta.parseString (evalStateT (runInner (evalIndentationParserT p indentst)) 0)

toError :: (Applicative m, Carrier sig m, Member (Error ErrInfo) sig) => Result a -> m a
toError (Success a) = pure a
toError (Failure e) = throwError e


indentst :: IndentationState
indentst = mkIndentationState 0 infIndentation True Gt

whole :: TokenParsing m => m a -> m a
whole p = p <* whiteSpace <* eof


identifier, operator :: (Monad m, TokenParsing m) => m String

identifier = ident (IdentifierStyle "identifier" letter (alphaNum <|> char '\'') reservedWords Identifier ReservedIdentifier)

-- | Parse an operator identifier.
--
-- >>> Trifecta.parseString operator mempty "$"
-- Success "$"
-- >>> Trifecta.parseString operator mempty ">"
-- Success ">"
operator = ident (IdentifierStyle "operator" (satisfy isOperator) (satisfy isOperator) reservedOperators Operator ReservedOperator)
  where isOperator '\'' = False
        isOperator c    = not (HashSet.member c reservedOperatorChars) && isPunctuation c || isSymbol c

reservedWords, reservedOperators :: HashSet.HashSet String
reservedWords     = HashSet.fromList [ "Type", "module", "import" ]
reservedOperators = HashSet.fromList [ "->", ".", ":" ]

reservedOperatorChars :: HashSet.HashSet Char
reservedOperatorChars = HashSet.fromList "(){}"

keyword, op :: TokenParsing m => String -> m String

keyword s = token (highlight ReservedIdentifier (try (string s <* notFollowedBy alphaNum))) <?> s

op s = token (highlight Operator (string s)) <?> s
