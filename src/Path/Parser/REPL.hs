module Path.Parser.REPL where

import Control.Applicative (Alternative(..))
import qualified Path.Parser.Module as M
import Path.Parser.Term
import Path.REPL.Command
import Text.Trifecta hiding (doc)

command :: DeltaParsing m => m (Maybe Command)
typeof, decl, eval, import' :: DeltaParsing m => m Command
quit, help, show', reload, doc :: (Monad m, TokenParsing m) => m Command
info :: (Monad m, TokenParsing m) => m Info

command = optional (quit <|> help <|> typeof <|> try decl <|> eval <|> show' <|> reload <|> import' <|> doc) <?> "command; use :? for help"

quit = Quit <$ token (string ":q") <|> Quit <$ token (string ":quit") <?> "quit"

help = Help <$ token (string ":h") <|> Help <$ token (string ":?") <|> Help <$ token (string ":help") <?> "help"

typeof = TypeOf <$ (token (string ":t") <|> token (string ":type")) <*> spanned term <?> "type of"

decl = Decl <$> M.declaration

eval = Eval <$> spanned term <?> "term"

show' = Show <$ token (string ":show") <*> info

info = Bindings <$ token (string "bindings") <|> Modules <$ token (string "modules")

reload = Reload <$ token (string ":r") <|> Reload <$ token (string ":reload") <?> "reload"

import' = Import <$> M.import'

doc = Doc <$ token (string ":doc") <*> M.moduleName
