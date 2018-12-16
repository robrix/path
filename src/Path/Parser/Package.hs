module Path.Parser.Package where

import Control.Applicative (Alternative(..))
import Path.Name
import Text.Parser.Token.Highlight
import Text.Trifecta

packageName :: (Monad m, TokenParsing m) => m PackageName
packageName = ident (IdentifierStyle "package name" letter (alphaNum <|> oneOf "-'_") mempty Identifier ReservedIdentifier)
