module Path.Parser.Module where

import Control.Applicative ((<**>), Alternative(..))
import qualified Path.Module as Module
import Path.Name
import Path.Parser
import Path.Parser.Term
import Path.Surface
import Path.Term
import Text.Trifecta
import Text.Trifecta.Indentation

module' :: (DeltaParsing m, IndentationParsing m, MonadFresh m) => FilePath -> m (Module.Module Name (Term (Surface Name) Span) Span)
module' path = flip Module.Module path <$ keyword "module" <*> moduleName <*> many (absoluteIndentation import') <*> many (absoluteIndentation declaration)

moduleName :: (Monad m, TokenParsing m) => m ModuleName
moduleName = makeModuleName <$> (identifier `sepByNonEmpty` dot)

import' :: DeltaParsing m => m (Module.Import Span)
import' = ann <$> spanned (Module.Import <$ keyword "import" <*> moduleName)
  where ann (f :~ a) = f a

declaration :: (DeltaParsing m, MonadFresh m) => m (Module.Decl Name (Term (Surface Name) Span))
declaration = name <**> (Module.Declare <$ op ":" <|> Module.Define <$ op "=") <*> term
