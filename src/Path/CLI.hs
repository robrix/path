{-# LANGUAGE TypeApplications #-}
module Path.CLI where

import Control.Carrier.Error.Either (runError)
import Control.Carrier.Lift (runM)
import Control.Monad (join)
import Data.Version (showVersion)
import Options.Applicative as Options
import Path.Error
import Path.Package
import Path.Parser (parseFile, whole)
import Path.Parser.Package as Parser (package)
import Path.Pretty
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
  =   flag' (either (prettyPrint @Notice) repl =<<) (short 'i' <> long "interactive" <> help "run interactively")
  <*> (pure . Right <$> some source <|> parsePackage <$> strOption (long "package-path" <> metavar "FILE" <> help "source file"))
  where parsePackage = fmap (fmap packageSources) . runM . runError . parseFile (whole Parser.package)


constraint :: Parser Constraint
constraint = Depends <$> strOption (short 'p' <> long "package" <> help "a package to depend on")

source :: Parser FilePath
source = strArgument (metavar "FILE" <> help "source file")

package :: Parser Package
package
  =   Package
  <$> strOption (short 'n' <> long "name" <> help "the name of the package")
  <*> many constraint
  <*> some source

versionString :: String
versionString = "pathc version " <> showVersion Library.version

version :: Options.Parser (a -> a)
version = infoOption versionString (long "version" <> short 'V' <> help "Output version info.")
