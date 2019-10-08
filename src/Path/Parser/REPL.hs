{-# LANGUAGE FlexibleContexts #-}
module Path.Parser.REPL where

import Control.Applicative (Alternative(..))
import Control.Effect.Parser
import Control.Effect.Reader
import Path.Parser
import qualified Path.Parser.Module as M
import Path.Parser.Term
import Path.REPL.Command
import Text.Parser.Char
import Text.Parser.Combinators
import Text.Parser.Token

command :: (Carrier sig m, Member Parser sig, Member (Reader [String]) sig, Member (Reader FilePath) sig, TokenParsing m) => m (Maybe Command)
typeof, eval, import', doc :: (Carrier sig m, Member Parser sig, Member (Reader [String]) sig, Member (Reader FilePath) sig, TokenParsing m) => m Command
decl :: (Carrier sig m, Member Parser sig, Member (Reader [String]) sig, Member (Reader FilePath) sig, TokenParsing m) => m Command
quit, help, show', reload :: (Monad m, TokenParsing m) => m Command

command = optional (quit <|> help <|> typeof <|> try decl <|> eval <|> show' <|> reload <|> import' <|> doc) <?> "command; use :? for help"

quit = Quit <$ token (string ":q") <|> Quit <$ token (string ":quit") <?> "quit"

help = Help <$ token (string ":h") <|> Help <$ token (string ":?") <|> Help <$ token (string ":help") <?> "help"

typeof = TypeOf <$ (token (string ":t") <|> token (string ":type")) <*> term <?> "type of"

decl = Decl <$> M.declaration

eval = Eval <$> term <?> "term"

show' = ShowModules <$ token (string ":show") <* token (string "modules")

reload = Reload <$ token (string ":r") <|> Reload <$ token (string ":reload") <?> "reload"

import' = Import <$> M.import'

doc = Doc <$ token (string ":doc") <*> spanned M.moduleName
