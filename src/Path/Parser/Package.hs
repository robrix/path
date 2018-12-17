module Path.Parser.Package where

import Control.Applicative (Alternative(..))
import Path.Name
import Path.Package
import Text.Parser.Token.Highlight
import Text.Trifecta
import Text.Trifecta.Indentation

package :: (IndentationParsing m, Monad m, TokenParsing m) => m Package
package
  =   Package
  <$> field "name" packageName'
  <*> pure []
  <*> field "sources" (some' filePath)

packageName' :: (Monad m, TokenParsing m) => m PackageName
packageName' = ident (IdentifierStyle "package name" letter (alphaNum <|> oneOf "-'_") mempty Identifier ReservedIdentifier)

filePath :: TokenParsing m => m FilePath
filePath = token ((alphaNum <|> char '.') `sepBy1` char '/')

some' :: (IndentationParsing m, TokenParsing m) => m a -> m [a]
some' m = commaSep1 (absoluteIndentation m)

field :: (IndentationParsing m, Monad m, TokenParsing m) => String -> m a -> m a
field name m = token (string name) *> colon *> localIndentation Gt m
