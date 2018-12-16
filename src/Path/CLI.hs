module Path.CLI where

import Data.Version (showVersion)
import Options.Applicative as Options
import qualified Paths_path as Library (version)

main :: IO ()
main = execParser argumentsParser

argumentsParser :: ParserInfo ()
argumentsParser = info
  (version <*> helper <*> options)
  (  fullDesc
  <> progDesc "Path is a small experiment in quantitative type theory."
  <> header   "Path - a quantitative, dependently-typed language")

options :: Parser ()
options = flag' () (short 'i' <> long "interactive" <> help "run interactively")

versionString :: String
versionString = "pathc version " <> showVersion Library.version

version :: Options.Parser (a -> a)
version = infoOption versionString (long "version" <> short 'V' <> help "Output version info.")
