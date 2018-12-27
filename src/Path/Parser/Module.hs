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

module' :: (DeltaParsing m, IndentationParsing m, MonadFresh m) => FilePath -> m (Module.Module Name (Term (Surface (Maybe Name) Name) Span))
module' path = make <$> optional docs <* keyword "module" <*> moduleName <*> many (absoluteIndentation import') <*> many (absoluteIndentation declaration)
  where make comment name = Module.Module name comment path

moduleName :: (Monad m, TokenParsing m) => m ModuleName
moduleName = makeModuleName <$> token (runUnspaced (identifier `sepByNonEmpty` dot))

import' :: DeltaParsing m => m Module.Import
import' = ann <$> spanned (Module.Import <$ keyword "import" <*> moduleName)
  where ann (f :~ a) = f a

declaration :: (DeltaParsing m, MonadFresh m) => m (Module.Decl Name (Term (Surface (Maybe Name) Name) Span))
declaration = (Module.Doc <$> docs <|> pure id) <*> decl
  where decl = name <**> (Module.Declare <$ op ":" <|> Module.Define <$ op "=") <*> term

docs :: TokenParsing m => m String
docs = runUnlined (fmap unlines . (:) <$> firstLine <*> many line)
  where firstLine = string "--" *> whiteSpace *> char '|' *> whiteSpace *> many (satisfy (/= '\n')) <* newline
        line = string "--" *> whiteSpace *> many (satisfy (/= '\n')) <* newline
