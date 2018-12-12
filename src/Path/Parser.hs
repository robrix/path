{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Path.Parser
( Parser
, parseFile
, parseString
, whole
, globalTerm
, keyword
, identifier
, op
, Span
) where

import Control.Applicative ((<**>), Alternative(..))
import Control.Monad.IO.Class
import Control.Monad (MonadPlus(..))
import qualified Data.ByteString.Char8 as BS
import Data.Char (isSpace)
import qualified Data.HashSet as HashSet
import Data.List (find)
import Data.Maybe (fromMaybe)
import qualified Path.Surface as Expr
import Path.Term hiding (ann)
import Path.Usage
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


globalTerm, type' :: DeltaParsing m => m (Term Expr.Surface Span)
globalTerm = term []

term, application, annotation, piType, functionType, forAll, var, lambda, atom :: DeltaParsing m => [String] -> m (Term Expr.Surface Span)

term = annotation

ann :: DeltaParsing m => m (f (Term f Span)) -> m (Term f Span)
ann = fmap respan . spanned
  where respan (f :~ a) = In f a

reann :: DeltaParsing m => m (Term f Span) -> m (Term f Span)
reann = fmap respan . spanned
  where respan (In f _ :~ a) = In f a


application vs = atom vs `chainl1` pure (Expr.#) <?> "function application"

type' = ann (Expr.typeT <$ keyword "Type")

forAll vs = reann (do
  (v, ty) <- op "∀" *> binding <* dot
  Expr.forAll (v, ty) <$> functionType (v : vs)) <?> "universally quantified type"
  where binding = (,) <$> identifier <* colon <*> term vs

piType vs = reann (do
  (v, mult, ty) <- braces ((,,) <$> identifier <* colon <*> optional multiplicity <*> term vs) <* op "->"
  ((v, fromMaybe More mult, ty) Expr.-->) <$> functionType (v : vs)) <?> "dependent function type"

annotation vs = functionType vs `chainr1` ((Expr..:) <$ op ":")

functionType vs = (,,) "_" <$> multiplicity <*> application vs <**> (flip (Expr.-->) <$ op "->" <*> functionType vs)
                <|> application vs <**> (flip arrow <$ op "->" <*> functionType vs <|> pure id)
                <|> piType vs
                <|> forAll vs
          where arrow = (Expr.-->) . (,,) "_" More

var vs = ann (toVar <$> identifier <?> "variable")
  where toVar n = maybe (Expr.global n) Expr.var (find (== n) vs)

lambda vs = reann (do
  vs' <- op "\\" *> some pattern <* dot
  bind vs' vs) <?> "lambda"
  where pattern = spanned (identifier <|> token (string "_")) <?> "pattern"
        bind [] vs = term vs
        bind ((v :~ a):vv) vs = Expr.lam (v, a) <$> bind vv (v:vs)

atom vs = var vs <|> type' <|> lambda vs <|> parens (term vs)

multiplicity :: (Monad m, TokenParsing m) => m Usage
multiplicity = Zero <$ keyword "0" <|> One <$ keyword "1"

identifier :: (Monad m, TokenParsing m) => m String
identifier = ident (IdentifierStyle "identifier" letter (alphaNum <|> char '\'') reservedWords Identifier ReservedIdentifier) <?> "identifier"

reservedWords :: HashSet.HashSet String
reservedWords =  HashSet.fromList [ "Type", "module", "where", "import" ]

keyword, op :: TokenParsing m => String -> m String

keyword s = token (highlight ReservedIdentifier (try (string s <* notFollowedBy alphaNum))) <?> s

op s = token (highlight Operator (string s)) <?> s
