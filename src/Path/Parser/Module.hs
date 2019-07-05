{-# LANGUAGE FlexibleContexts, TypeOperators #-}
module Path.Parser.Module where

import Control.Applicative (Alternative(..))
import Control.Effect
import Control.Monad.IO.Class
import qualified Data.Text.Encoding as Text
import qualified Path.Module as Module
import Path.Name hiding (name)
import Path.Parser
import Path.Parser.Term
import Path.Pretty (Doc)
import Path.Surface
import Text.Trifecta
import Text.Trifecta.Indentation

parseModule :: (Carrier sig m, Member (Error Doc) sig, MonadIO m) => FilePath -> m (Module.Module Surface User)
parseModule = flip parseFile <*> whole . module'


module' :: (DeltaParsing m, IndentationParsing m) => FilePath -> m (Module.Module Surface User)
module' path = make <$> optional docs <* keyword "module" <*> moduleName <*> many (absoluteIndentation import') <*> many (absoluteIndentation declaration)
  where make comment name is = Module.module' name comment path is . map ((,) . Module.declName <*> id)

moduleName :: (Monad m, TokenParsing m) => m ModuleName
moduleName = makeModuleName <$> token (runUnspaced (identifier `sepByNonEmpty` dot))

import' :: DeltaParsing m => m (Spanned ModuleName)
import' = spanned (keyword "import" *> moduleName)

declaration :: (DeltaParsing m, IndentationParsing m) => m (Module.Decl (Surface User))
declaration = do
  docs <- optional docs
  ((name, name'), ty) <- absoluteIndentation ((,) <$> slicedWith (,) name <* op ":" <*> term)
  tm <- absoluteIndentation (token (text (Text.decodeUtf8 name')) *> op "=" *> term)
  pure (Module.Decl name docs tm ty)

docs :: TokenParsing m => m String
docs = runUnlined (fmap unlines . (:) <$> firstLine <*> many line)
  where firstLine = string "--" *> whiteSpace *> char '|' *> whiteSpace *> many (satisfy (/= '\n')) <* newline
        line = string "--" *> whiteSpace *> many (satisfy (/= '\n')) <* newline
