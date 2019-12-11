{-# LANGUAGE FlexibleContexts, TypeOperators #-}
module Path.Parser.Module where

import Control.Algebra
import Control.Applicative (Alternative(..))
import Control.Effect.Error
import Control.Effect.Parser
import Control.Effect.Reader
import Control.Monad.IO.Class
import Path.Error (Notice)
import qualified Path.Module as Module
import Path.Name
import Path.Parser
import Path.Parser.Term
import Path.Span (Spanned(..))
import Path.Surface
import Text.Parser.Char
import Text.Parser.Combinators
import Text.Parser.Token

parseModule :: (Effect sig, Has (Error Notice) sig m, MonadIO m) => FilePath -> m (Module.Module Surface User)
parseModule path = parseFile (whole (module' path)) path


module' :: (Has Parser sig m, Has (Reader Lines) sig m, Has (Reader Path) sig m, TokenParsing m) => FilePath -> m (Module.Module Surface User)
module' path = make <$> optional docs <* keyword "module" <*> moduleName <*> many (try import') <*> many declaration
  where make comment name = Module.module' name comment path

moduleName :: (Monad m, TokenParsing m) => m ModuleName
moduleName = makeModuleName <$> token (runUnspaced (identifier `sepByNonEmpty` dot))

import' :: (Has Parser sig m, Has (Reader Lines) sig m, Has (Reader Path) sig m, TokenParsing m) => m (Spanned ModuleName)
import' = spanned (keyword "import" *> moduleName) <* semi

declaration :: (Has Parser sig m, Has (Reader Lines) sig m, Has (Reader Path) sig m, TokenParsing m) => m (Module.Decl (Surface User))
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
