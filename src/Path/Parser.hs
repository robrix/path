{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Path.Parser where

import Control.Applicative (Alternative(..))
import Control.Monad.IO.Class
import Control.Monad (MonadPlus(..))
import qualified Data.ByteString.Char8 as BS
import Data.Char (isSpace)
import qualified Data.HashSet as HashSet
import Data.List (elemIndex)
import qualified Path.Expr as Expr
import Text.Parser.Char
import Text.Parser.Combinators
import Text.Parser.LookAhead
import Text.Parser.Token
import Text.Parser.Token.Highlight
import Text.Parser.Token.Style
import qualified Text.Trifecta as Trifecta
import Text.Trifecta.Delta
import Text.Trifecta.Indentation

type Parser = IndentationParserT Char Inner
-- type MonadParsing m = (IndentationParsing m, Monad m, TokenParsing m)

newtype Inner a = Inner { runInner :: Trifecta.Parser a }
  deriving (Alternative, Applicative, CharParsing, Trifecta.DeltaParsing, Functor, LookAheadParsing, Trifecta.MarkParsing Delta, Monad, MonadPlus, Parsing)

instance TokenParsing Inner where
  someSpace = Inner $ buildSomeSpaceParser (skipSome (satisfy isSpace)) haskellCommentStyle
  nesting = Inner . nesting . runInner
  highlight h = Inner . highlight h . runInner


parseFile :: MonadIO m => Parser a -> FilePath -> m (Maybe a)
parseFile p = Trifecta.parseFromFile (runInner (whiteSpace *> evalIndentationParserT p indentst))

parseString :: Parser a -> String -> Either String a
parseString p = toResult . Trifecta.parseString (runInner (evalIndentationParserT p indentst)) directed

toResult :: Trifecta.Result a -> Either String a
toResult r = case r of
  Trifecta.Success a -> Right a
  Trifecta.Failure info -> Left (show (Trifecta._errDoc info))


directed :: Delta
directed = Directed BS.empty 0 0 0 0

indentst :: IndentationState
indentst = mkIndentationState 0 infIndentation True Gt

whole :: TokenParsing m => m a -> m a
whole p = whiteSpace *> p <* eof

globalTerm, type' :: (Monad m, TokenParsing m) => m (Expr.Term Expr.Surface)
globalTerm = term []

term, piType, functionType, var, atom :: (Monad m, TokenParsing m) => [String] -> m (Expr.Term Expr.Surface)

term _ = type'

type' = Expr.typeT <$ keyword "Type"

piType vs = (do
  (v, ty) <- parens ((,) <$> identifier <* colon <*> term vs) <* op "->"
  (ty Expr.-->) <$> piType (v : vs)) <?> "dependent function type"

functionType vs = makePi <$> type' <*> optional (op "->" *> piType vs) <?> "function type"
  where makePi ty1 Nothing = ty1
        makePi ty1 (Just ty2) = ty1 Expr.--> ty2

var vs = toVar <$> identifier <?> "variable"
  where toVar n = maybe (Expr.global n) Expr.var (elemIndex n vs)

atom vs = var vs <|> type'

identifier :: (Monad m, TokenParsing m) => m String
identifier = ident (IdentifierStyle "identifier" letter (alphaNum <|> char '\'') reservedWords Identifier ReservedIdentifier) <?> "identifier"

reservedWords :: HashSet.HashSet String
reservedWords =  HashSet.fromList [ "Type" ]

keyword, op :: TokenParsing m => String -> m String

keyword s = token (highlight ReservedIdentifier (try (string s <* notFollowedBy alphaNum))) <?> s

op s = token (highlight Operator (string s)) <?> s
