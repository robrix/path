{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Path.Parser where

import Control.Applicative ((<**>), Alternative(..))
import Control.Monad.IO.Class
import Control.Monad (MonadPlus(..))
import qualified Data.ByteString.Char8 as BS
import Data.Char (isSpace)
import qualified Data.HashSet as HashSet
import Data.List (find)
import Path.Decl
import Path.Plicity
import qualified Path.Surface as Expr
import Path.Term
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


parseFile :: MonadIO m => Parser a -> FilePath -> m (Either String a)
parseFile p = fmap toResult . Trifecta.parseFromFileEx (runInner (whiteSpace *> evalIndentationParserT p indentst))

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
  | TypeOf (Term Expr.Surface)
  | Decl Decl
  | Eval (Term Expr.Surface)
  | Show Info
  | Load ModuleName
  deriving (Eq, Ord, Show)

data Info
  = Bindings
  deriving (Eq, Ord, Show)

command, quit, help, typeof, decl, eval, show', load :: (Monad m, TokenParsing m) => m Command

command = quit <|> help <|> typeof <|> try decl <|> eval <|> show' <|> load <?> "command; use :? for help"

quit = Quit <$ token (string ":q") <|> Quit <$ token (string ":quit") <?> "quit"

help = Help <$ token (string ":h") <|> Help <$ token (string ":?") <|> Help <$ token (string ":help") <?> "help"

typeof = TypeOf <$ (token (string ":t") <|> token (string ":type")) <*> globalTerm <?> "type of"

decl = Decl <$> declaration

eval = Eval <$> globalTerm <?> "term"

show' = Show Bindings <$ token (string ":show") <* token (string "bindings")

load = Load <$ token (string ":load") <*> moduleName


module' :: (Monad m, IndentationParsing m, TokenParsing m) => m Module
module' = Module <$ keyword "module" <*> moduleName <* keyword "where" <*> absoluteIndentation (many declaration)

moduleName :: (Monad m, TokenParsing m) => m ModuleName
moduleName = identifier `sepByNonEmpty` dot

declaration :: (Monad m, TokenParsing m) => m Decl
declaration = identifier <**> (Declare <$ op ":" <|> Define  <$ op "=") <*> globalTerm


globalTerm, type' :: (Monad m, TokenParsing m) => m (Term Expr.Surface)
globalTerm = term []

term, application, annotation, var, lambda, atom :: (Monad m, TokenParsing m) => [String] -> m (Term Expr.Surface)

piType, functionType :: (Monad m, TokenParsing m) => Int -> [String] -> m (Term Expr.Surface)

term = annotation

application vs = atom vs `chainl1` pure (Expr.#) <?> "function application"

type' = Expr.typeT <$ keyword "Type"

piType i vs = (do
  (v, ty) <- braces ((,) <$> identifier <* colon <*> term vs) <* op "->"
  ((v, Explicit, ty) Expr.-->) <$> functionType i (v : vs)) <?> "dependent function type"

annotation vs = functionType 0 vs `chainr1` ((Expr..:) <$ op ":")

functionType i vs = application vs <**> (flip arrow <$ op "->" <*> functionType (succ i) vs <|> pure id)
              <|> piType i vs
          where arrow = (Expr.-->) . (,,) ('_' : show i) Explicit

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
