module Path.Parser.Module where

import Control.Applicative ((<**>), Alternative(..))
import Path.Decl
import qualified Path.Module as Module
import Path.Name
import Path.Parser
import Path.Parser.Term
import Path.Surface
import Path.Term
import Text.Trifecta
import Text.Trifecta.Indentation

module' :: (DeltaParsing m, IndentationParsing m, MonadFresh m) => FilePath -> m (Module.Module Name (Term (Surface Name) Span) Span)
module' path = flip Module.Module path <$ keyword "module" <*> moduleName <* keyword "where" <*> many (absoluteIndentation import') <*> many (absoluteIndentation declaration)

moduleName :: (Monad m, TokenParsing m) => m ModuleName
moduleName = makeModuleName <$> (identifier `sepByNonEmpty` dot)

import' :: (Monad m, TokenParsing m) => m (Module.Import Span)
import' = Module.Import <$ keyword "import" <*> moduleName

declaration :: (DeltaParsing m, MonadFresh m) => m (Decl Name (Term (Surface Name) Span))
declaration = name <**> (Declare <$ op ":" <|> Define <$ op "=") <*> term
