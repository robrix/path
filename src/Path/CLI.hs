module Path.CLI where

import Control.Monad (join)
import Data.Version (showVersion)
import Options.Applicative as Options
import Path.Package
import Path.REPL
import qualified Paths_path as Library (version)

main :: IO ()
main = join (execParser argumentsParser)

argumentsParser :: ParserInfo (IO ())
argumentsParser = info
  (version <*> helper <*> options)
  (  fullDesc
  <> progDesc "Path is a small experiment in quantitative type theory."
  <> header   "Path - a quantitative, dependently-typed language")

options :: Parser (IO ())
options
  =   flag' repl (short 'i' <> long "interactive" <> help "run interactively")
  <*> some source


constraint :: Parser Constraint
constraint = Depends <$> strOption (short 'p' <> long "package" <> help "a package to depend on")

source :: Parser FilePath
source = strArgument (metavar "FILES" <> help "source files")

package :: Parser Package
package
  =   Package
  <$> strOption (short 'n' <> long "name" <> help "the name of the package")
  <*> some constraint
  <*> some source

versionString :: String
versionString = "pathc version " <> showVersion Library.version

version :: Options.Parser (a -> a)
version = infoOption versionString (long "version" <> short 'V' <> help "Output version info.")
