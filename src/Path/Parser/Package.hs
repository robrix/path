module Path.Parser.Package where

import Control.Applicative (Alternative(..))
import Path.Name
import Text.Parser.Token.Highlight
import Text.Trifecta
import Text.Trifecta.Indentation

packageName :: (Monad m, TokenParsing m) => m PackageName
packageName = ident (IdentifierStyle "package name" letter (alphaNum <|> oneOf "-'_") mempty Identifier ReservedIdentifier)

some' :: (IndentationParsing m, TokenParsing m) => m a -> m [a]
some' m = commaSep1 (absoluteIndentation m)

field :: (IndentationParsing m, Monad m, TokenParsing m) => String -> m a -> m a
field name m = token (string name) *> colon *> localIndentation Gt m
