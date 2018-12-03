{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Path.Parser where

import Control.Applicative ((<**>), Alternative(..))
import Control.Monad.IO.Class
import Control.Monad (MonadPlus(..))
import qualified Data.ByteString.Char8 as BS
import Data.Char (isSpace)
import qualified Data.HashSet as HashSet
import Data.List (find)
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


data Command
  = Quit
  | Help
  | Type (Expr.Term Expr.Surface)
  | Eval (Expr.Term Expr.Surface)
  deriving (Eq, Ord, Show)


definition :: (Monad m, IndentationParsing m, TokenParsing m) => m (String, Expr.Term Expr.Surface)
definition = (,) <$> identifier <* op "=" <*> localIndentation Gt globalTerm


globalTerm, type' :: (Monad m, TokenParsing m) => m (Expr.Term Expr.Surface)
globalTerm = term []

term, application, annotation, var, lambda, atom :: (Monad m, TokenParsing m) => [String] -> m (Expr.Term Expr.Surface)

piType, functionType :: (Monad m, TokenParsing m) => Int -> [String] -> m (Expr.Term Expr.Surface)

term = annotation

application vs = atom vs `chainl1` pure (Expr.#) <?> "function application"

type' = Expr.typeT <$ keyword "Type"

piType i vs = (do
  (v, ty) <- braces ((,) <$> identifier <* colon <*> term vs) <* op "->"
  ((v, ty) Expr.-->) <$> functionType i (v : vs)) <?> "dependent function type"

annotation vs = functionType 0 vs `chainr1` ((Expr..:) <$ op ":")

functionType i vs = application vs <**> (flip arrow <$ op "->" <*> functionType (succ i) vs <|> pure id)
              <|> piType i vs
          where arrow = (Expr.-->) . (,) ('_' : show i)

var vs = toVar <$> identifier <?> "variable"
  where toVar n = maybe (Expr.global n) Expr.var (find (== n) vs)

lambda vs = (do
  vs' <- op "\\" *> some pattern <* dot
  bind vs' vs) <?> "lambda"
  where pattern = identifier <|> token (string "_") <?> "pattern"
        bind [] vs = term vs
        bind (v:vv) vs = Expr.lam v <$> bind vv (v:vs)

atom vs = var vs <|> type' <|> lambda vs <|> parens (term vs)

identifier :: (Monad m, TokenParsing m) => m String
identifier = ident (IdentifierStyle "identifier" letter (alphaNum <|> char '\'') reservedWords Identifier ReservedIdentifier) <?> "identifier"

reservedWords :: HashSet.HashSet String
reservedWords =  HashSet.fromList [ "Type" ]

keyword, op :: TokenParsing m => String -> m String

keyword s = token (highlight ReservedIdentifier (try (string s <* notFollowedBy alphaNum))) <?> s

op s = token (highlight Operator (string s)) <?> s
