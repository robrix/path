{-# LANGUAGE FlexibleContexts, TypeOperators #-}
module Path.Parser.Module where

import Control.Applicative (Alternative(..))
import Control.Effect
import Control.Monad.IO.Class
import qualified Path.Module as Module
import Path.Name hiding (name)
import Path.Parser
import Path.Parser.Term
import Path.Pretty (Doc)
import Path.Surface
import Path.Term
import Text.Trifecta

parseModule :: (Carrier sig m, Member (Error Doc) sig, MonadIO m) => FilePath -> m (Module.Module (Term Surface) User)
parseModule = flip parseFile <*> whole . module'


module' :: DeltaParsing m => FilePath -> m (Module.Module (Term Surface) User)
module' path = make <$> optional docs <* keyword "module" <*> moduleName <*> many (try import') <*> many declaration
  where make comment name = Module.module' name comment path

moduleName :: (Monad m, TokenParsing m) => m ModuleName
moduleName = makeModuleName <$> token (runUnspaced (identifier `sepByNonEmpty` dot))

import' :: DeltaParsing m => m (Spanned ModuleName)
import' = spanned (keyword "import" *> moduleName) <* semi

declaration :: DeltaParsing m => m (Module.Decl (Term Surface User))
declaration = do
  docs <- optional docs
  name <- name
  ty <- op ":" *> term
  tm <- op "=" *> term
  Module.Decl name docs tm ty <$ semi

docs :: TokenParsing m => m String
docs = runUnlined (fmap unlines . (:) <$> firstLine <*> many line)
  where firstLine = string "--" *> whiteSpace *> char '|' *> whiteSpace *> many (satisfy (/= '\n')) <* newline
        line = string "--" *> whiteSpace *> many (satisfy (/= '\n')) <* newline
