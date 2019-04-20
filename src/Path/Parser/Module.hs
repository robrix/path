{-# LANGUAGE FlexibleContexts #-}
module Path.Parser.Module where

import Control.Applicative ((<**>), Alternative(..))
import Control.Effect
import Control.Monad.IO.Class
import qualified Path.Module as Module
import Path.Name
import Path.Parser
import Path.Parser.Term
import Path.Pretty (Doc)
import Path.Surface
import Text.Trifecta
import Text.Trifecta.Indentation

parseModule :: (Carrier sig m, Member (Error Doc) sig, MonadIO m) => FilePath -> m (Module.Module User (Spanned Surface))
parseModule = flip parseFile <*> whole . module'


module' :: (DeltaParsing m, IndentationParsing m) => FilePath -> m (Module.Module User (Spanned Surface))
module' path = make <$> optional docs <* keyword "module" <*> moduleName <*> many (absoluteIndentation import') <*> many (absoluteIndentation declaration)
  where make comment name = Module.Module name comment path

moduleName :: (Monad m, TokenParsing m) => m ModuleName
moduleName = makeModuleName <$> token (runUnspaced (identifier `sepByNonEmpty` dot))

import' :: DeltaParsing m => m (Spanned Module.Import)
import' = spanned (Module.Import <$ keyword "import" <*> moduleName)

declaration :: DeltaParsing m => m (Spanned (Module.Decl User (Spanned Surface)))
declaration = spanned (Module.Doc <$> docs <*> decl) <|> decl
  where decl = spanned (name <**> (Module.Declare <$ op ":" <|> Module.Define <$ op "=") <*> term)

docs :: TokenParsing m => m String
docs = runUnlined (fmap unlines . (:) <$> firstLine <*> many line)
  where firstLine = string "--" *> whiteSpace *> char '|' *> whiteSpace *> many (satisfy (/= '\n')) <* newline
        line = string "--" *> whiteSpace *> many (satisfy (/= '\n')) <* newline
