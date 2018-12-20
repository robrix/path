{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Path.Parser
( Parser(..)
, parseFile
, parseString
, whole
, keyword
, identifier
, operator
, reservedWords
, reservedOperators
, op
, LayoutParsing(..)
, ErrInfo
, Span
) where

import Control.Applicative (Alternative(..))
import Control.Effect
import Control.Effect.Error
import Control.Monad (MonadPlus(..), (<=<))
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.State
import Data.Char (isPunctuation, isSpace, isSymbol)
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

data Layout = Indent | Braces
  deriving (Eq, Ord, Show)

newtype Parser a = Parser { runParser :: StateT Int (ReaderT Layout Trifecta.Parser) a }
  deriving (Alternative, Applicative, CharParsing, DeltaParsing, Functor, LookAheadParsing, MarkParsing Delta, Monad, MonadPlus, Parsing)

instance TokenParsing Parser where
  someSpace = Parser $ buildSomeSpaceParser (skipSome (satisfy isSpace)) haskellCommentStyle
  nesting = Parser . nesting . runParser
  highlight h = Parser . highlight h . runParser
  token p = (someSpace <|> pure ()) *> p


parseFile :: (Carrier sig m, Member (Error ErrInfo) sig, MonadIO m) => Parser a -> FilePath -> m a
parseFile p = toError <=< parseFromFileEx (runReaderT (evalStateT (runParser p) 0) Indent)

parseString :: (Carrier sig m, Member (Error ErrInfo) sig, MonadIO m) => Parser a -> String -> m a
parseString p = toError . Trifecta.parseString (runReaderT (evalStateT (runParser p) 0) Indent) mempty

toError :: (Applicative m, Carrier sig m, Member (Error ErrInfo) sig) => Result a -> m a
toError (Success a) = pure a
toError (Failure e) = throwError e


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


class DeltaParsing m => LayoutParsing m where
  layout :: m a -> m a

instance LayoutParsing Parser where
  layout = id
