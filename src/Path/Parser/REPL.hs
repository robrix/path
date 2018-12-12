module Path.Parser.REPL where

import Control.Applicative (Alternative(..))
import qualified Path.Parser.Module as M
import Path.Parser.Term
import Path.REPL.Command
import Text.Trifecta

command, typeof, decl, eval :: DeltaParsing m => m Command
quit, help, show', load, reload, import' :: (Monad m, TokenParsing m) => m Command

command = quit <|> help <|> typeof <|> try decl <|> eval <|> show' <|> load <|> reload <|> import' <?> "command; use :? for help"

quit = Quit <$ token (string ":q") <|> Quit <$ token (string ":quit") <?> "quit"

help = Help <$ token (string ":h") <|> Help <$ token (string ":?") <|> Help <$ token (string ":help") <?> "help"

typeof = TypeOf <$ (token (string ":t") <|> token (string ":type")) <*> globalTerm <?> "type of"

decl = Decl <$> M.declaration

eval = Eval <$> globalTerm <?> "term"

show' = Show Bindings <$ token (string ":show") <* token (string "bindings")

load = Load <$ token (string ":load") <*> M.moduleName

reload = Reload <$ token (string ":r") <|> Reload <$ token (string ":reload") <?> "reload"

import' = Import <$> M.import'
