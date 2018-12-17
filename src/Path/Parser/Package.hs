module Path.Parser.Package where

import Control.Applicative (Alternative(..))
import Data.List (intercalate)
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
  <*> field "sources" (commaSep1 filePath)

packageName' :: (Monad m, TokenParsing m) => m PackageName
packageName' = ident (IdentifierStyle "package name" letter (alphaNum <|> oneOf "-_") mempty Identifier ReservedIdentifier)

filePath :: TokenParsing m => m FilePath
filePath = intercalate "/" <$> token (some (alphaNum <|> char '.') `sepBy1` string "/")

field :: (IndentationParsing m, Monad m, TokenParsing m) => String -> m a -> m a
field name m = absoluteIndentation (token (string name) *> colon *> m)
