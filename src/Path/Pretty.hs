module Path.Pretty where

import Data.Text.Lazy
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal hiding (putDoc)
import System.Console.Terminal.Size as Size
import System.IO (stdout)

prettyPrint :: Pretty a => a -> IO ()
prettyPrint = putDoc . pretty

putDoc :: Doc AnsiStyle -> IO ()
putDoc doc = do
  options <- layoutOptions
  renderIO stdout (layoutPretty options (doc <> line))

showDocIO :: Doc AnsiStyle -> IO String
showDocIO doc = do
  options <- layoutOptions
  pure (unpack (renderLazy (layoutPretty options doc)))

layoutOptions :: IO LayoutOptions
layoutOptions = do
  s <- maybe 80 Size.width <$> size
  pure LayoutOptions { layoutPageWidth = AvailablePerLine s 1 }


class PrettyPrec a where
  prettyPrec :: Int -> a -> Doc ann

prettyParens :: Bool -> Doc ann -> Doc ann
prettyParens True = parens
prettyParens False = id

prettyBraces :: Bool -> Doc ann -> Doc ann
prettyBraces True = braces
prettyBraces False = id
