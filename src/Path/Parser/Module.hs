module Path.Parser.Module where

import Control.Applicative ((<**>), Alternative(..))
import Path.Decl
import qualified Path.Module as Module
import Path.Parser
import Path.Parser.Term
import Path.Surface
import Path.Term
import Text.Trifecta
import Text.Trifecta.Indentation

module' :: (DeltaParsing m, IndentationParsing m) => m (Module.Module (Term Surface Span))
module' = Module.Module <$ keyword "module" <*> moduleName <* keyword "where" <*> many (absoluteIndentation import') <*> many (absoluteIndentation declaration)

moduleName :: (Monad m, TokenParsing m) => m Module.ModuleName
moduleName = Module.makeModuleName <$> (identifier `sepByNonEmpty` dot)

import' :: (Monad m, TokenParsing m) => m Module.Import
import' = Module.Import <$ keyword "import" <*> moduleName

declaration :: DeltaParsing m => m (Decl (Term Surface Span))
declaration = identifier <**> (Declare <$ op ":" <|> Define <$ op "=") <*> globalTerm
