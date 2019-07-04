module Path.Parser.REPL where

import Control.Applicative (Alternative(..))
import qualified Path.Parser.Module as M
import Path.Parser.Term
import Path.REPL.Command
import Text.Trifecta hiding (doc)
import Text.Trifecta.Indentation

command :: (DeltaParsing m, IndentationParsing m) => m (Maybe Command)
typeof, eval, import' :: DeltaParsing m => m Command
decl :: (DeltaParsing m, IndentationParsing m) => m Command
quit, help, show', reload, doc :: (Monad m, TokenParsing m) => m Command
info :: (Monad m, TokenParsing m) => m Info

command = optional (quit <|> help <|> typeof <|> try decl <|> eval <|> show' <|> reload <|> import' <|> doc) <?> "command; use :? for help"

quit = Quit <$ token (string ":q") <|> Quit <$ token (string ":quit") <?> "quit"

help = Help <$ token (string ":h") <|> Help <$ token (string ":?") <|> Help <$ token (string ":help") <?> "help"

typeof = TypeOf <$ (token (string ":t") <|> token (string ":type")) <*> term <?> "type of"

decl = Decl . snd <$> M.declaration

eval = Eval <$> term <?> "term"

show' = Show <$ token (string ":show") <*> info

info = Bindings <$ token (string "bindings") <|> Modules <$ token (string "modules")

reload = Reload <$ token (string ":r") <|> Reload <$ token (string ":reload") <?> "reload"

import' = Import <$> M.import'

doc = Doc <$ token (string ":doc") <*> M.moduleName
