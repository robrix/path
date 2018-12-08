{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Path.Parser
( Parser
, parseFile
, parseString
, whole
, Command(..)
, Info(..)
, command
, module'
, Span
) where

import Control.Applicative ((<**>), Alternative(..))
import Control.Monad.IO.Class
import Control.Monad (MonadPlus(..))
import qualified Data.ByteString.Char8 as BS
import Data.Char (isSpace)
import qualified Data.HashSet as HashSet
import Data.List (find)
import qualified Path.Decl as Decl
import qualified Path.Module as Module
import Path.Plicity
import qualified Path.Surface as Expr
import Path.Term hiding (ann)
import Text.Parser.Char
import Text.Parser.Combinators
import Text.Parser.LookAhead
import Text.Parser.Token
import Text.Parser.Token.Highlight
import Text.Parser.Token.Style
import Text.PrettyPrint.ANSI.Leijen (Doc)
import qualified Text.Trifecta as Trifecta
import Text.Trifecta hiding (Parser, parseString)
import Text.Trifecta.Delta
import Text.Trifecta.Indentation

type Parser = IndentationParserT Char Inner

newtype Inner a = Inner { runInner :: Trifecta.Parser a }
  deriving (Alternative, Applicative, CharParsing, DeltaParsing, Functor, LookAheadParsing, MarkParsing Delta, Monad, MonadPlus, Parsing)

instance TokenParsing Inner where
  someSpace = Inner $ buildSomeSpaceParser (skipSome (satisfy isSpace)) haskellCommentStyle
  nesting = Inner . nesting . runInner
  highlight h = Inner . highlight h . runInner


parseFile :: MonadIO m => Parser a -> FilePath -> m (Either Doc a)
parseFile p = fmap toResult . parseFromFileEx (runInner (whiteSpace *> evalIndentationParserT p indentst))

parseString :: Parser a -> String -> Either Doc a
parseString p = toResult . Trifecta.parseString (runInner (evalIndentationParserT p indentst)) directed

toResult :: Result a -> Either Doc a
toResult = foldResult (Left . _errDoc) Right


directed :: Delta
directed = Directed BS.empty 0 0 0 0

indentst :: IndentationState
indentst = mkIndentationState 0 infIndentation True Gt

whole :: TokenParsing m => m a -> m a
whole p = whiteSpace *> p <* eof


data Command
  = Quit
  | Help
  | TypeOf (Term (Ann Expr.Surface Span))
  | Decl (Decl.Decl (Term (Ann Expr.Surface Span)))
  | Eval (Term (Ann Expr.Surface Span))
  | Show Info
  | Load Module.ModuleName
  deriving (Eq, Ord, Show)

data Info
  = Bindings
  deriving (Eq, Ord, Show)

command, typeof, decl, eval :: DeltaParsing m => m Command
quit, help, show', load :: (Monad m, TokenParsing m) => m Command

command = quit <|> help <|> typeof <|> try decl <|> eval <|> show' <|> load <?> "command; use :? for help"

quit = Quit <$ token (string ":q") <|> Quit <$ token (string ":quit") <?> "quit"

help = Help <$ token (string ":h") <|> Help <$ token (string ":?") <|> Help <$ token (string ":help") <?> "help"

typeof = TypeOf <$ (token (string ":t") <|> token (string ":type")) <*> globalTerm <?> "type of"

decl = Decl <$> declaration

eval = Eval <$> globalTerm <?> "term"

show' = Show Bindings <$ token (string ":show") <* token (string "bindings")

load = Load <$ token (string ":load") <*> moduleName


module' :: (DeltaParsing m, IndentationParsing m) => m (Module.Module (Term (Ann Expr.Surface Span)))
module' = Module.Module <$ keyword "module" <*> moduleName <* keyword "where" <*> many import' <*> many (absoluteIndentation declaration)

moduleName :: (Monad m, TokenParsing m) => m Module.ModuleName
moduleName = Module.makeModuleName <$> (identifier `sepByNonEmpty` dot)

import' :: (Monad m, TokenParsing m) => m Module.Import
import' = Module.Import <$ keyword "import" <*> moduleName

declaration :: DeltaParsing m => m (Decl.Decl (Term (Ann Expr.Surface Span)))
declaration = identifier <**> (Decl.Declare <$ op ":" <|> Decl.Define  <$ op "=") <*> globalTerm


globalTerm, type' :: DeltaParsing m => m (Term (Ann Expr.Surface Span))
globalTerm = term []

term, application, annotation, var, lambda, atom :: DeltaParsing m => [String] -> m (Term (Ann Expr.Surface Span))

piType, functionType :: DeltaParsing m => Int -> [String] -> m (Term (Ann Expr.Surface Span))

term = annotation

ann :: DeltaParsing m => m (f (Term (Ann f Span))) -> m (Term (Ann f Span))
ann = fmap respan . spanned
  where respan (f :~ a) = In (Ann f a)

reann :: DeltaParsing m => m (Term (Ann f Span)) -> m (Term (Ann f Span))
reann = fmap respan . spanned
  where respan (In (Ann f _) :~ a) = In (Ann f a)


application vs = atom vs `chainl1` pure (Expr.#) <?> "function application"

type' = ann (Expr.typeT <$ keyword "Type")

piType i vs = reann (do
  (v, ty) <- braces ((,) <$> identifier <* colon <*> term vs) <* op "->"
  ((v, Explicit, ty) Expr.-->) <$> functionType i (v : vs)) <?> "dependent function type"

annotation vs = functionType 0 vs `chainr1` ((Expr..:) <$ op ":")

functionType i vs = application vs <**> (flip arrow <$ op "->" <*> functionType (succ i) vs <|> pure id)
                <|> piType i vs
          where arrow = (Expr.-->) . (,,) ('_' : show i) Explicit

var vs = ann (toVar <$> identifier <?> "variable")
  where toVar n = maybe (Expr.global n) Expr.var (find (== n) vs)

lambda vs = reann (do
  vs' <- op "\\" *> some pattern <* dot
  bind vs' vs) <?> "lambda"
  where pattern = spanned (identifier <|> token (string "_")) <?> "pattern"
        bind [] vs = term vs
        bind ((v :~ a):vv) vs = Expr.lam (v, a) <$> bind vv (v:vs)

atom vs = var vs <|> type' <|> lambda vs <|> parens (term vs)

identifier :: (Monad m, TokenParsing m) => m String
identifier = ident (IdentifierStyle "identifier" letter (alphaNum <|> char '\'') reservedWords Identifier ReservedIdentifier) <?> "identifier"

reservedWords :: HashSet.HashSet String
reservedWords =  HashSet.fromList [ "Type", "module", "where", "import" ]

keyword, op :: TokenParsing m => String -> m String

keyword s = token (highlight ReservedIdentifier (try (string s <* notFollowedBy alphaNum))) <?> s

op s = token (highlight Operator (string s)) <?> s
