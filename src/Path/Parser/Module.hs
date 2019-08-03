{-# LANGUAGE FlexibleContexts, TypeOperators #-}
module Path.Parser.Module where

import Control.Applicative (Alternative(..))
import Control.Effect
import Control.Monad.IO.Class
import qualified Path.Module as Module
import Path.Name
import Path.Parser
import Path.Parser.Term
import Path.Pretty (Notice)
import Path.Span (Spanned(..))
import Path.Surface
import Path.Term
import Text.Parser.Char
import Text.Parser.Combinators
import Text.Parser.Token

parseModule :: (Carrier sig m, Effect sig, Member (Error Notice) sig, MonadIO m) => FilePath -> m (Module.Module (Term Surface) User)
parseModule path = parseFile (whole (module' path)) path


module' :: (Carrier sig m, Member Parser sig, Member (Reader [String]) sig, Member (Reader FilePath) sig, TokenParsing m) => FilePath -> m (Module.Module (Term Surface) User)
module' path = make <$> optional docs <* keyword "module" <*> moduleName <*> many (try import') <*> many declaration
  where make comment name = Module.module' name comment path

moduleName :: (Monad m, TokenParsing m) => m ModuleName
moduleName = makeModuleName <$> token (runUnspaced (identifier `sepByNonEmpty` dot))

import' :: (Carrier sig m, Member Parser sig, Member (Reader [String]) sig, Member (Reader FilePath) sig, TokenParsing m) => m (Spanned ModuleName)
import' = spanned (keyword "import" *> moduleName) <* semi

declaration :: (Carrier sig m, Member Parser sig, Member (Reader [String]) sig, Member (Reader FilePath) sig, TokenParsing m) => m (Module.Decl (Term Surface User))
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
