module Path.Pretty where

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal
import System.Console.Terminal.Size as Size
import System.IO (stdout)

putDoc :: Doc AnsiStyle -> IO ()
putDoc doc = do
  options <- layoutOptions
  renderIO stdout (layoutPretty options (doc <> line))

layoutOptions :: IO LayoutOptions
layoutOptions = do
  s <- maybe 80 Size.width <$> size
  pure LayoutOptions { layoutPageWidth = AvailablePerLine s 1 }


class PrettyPrec a where
  prettyPrec :: Int -> a -> Doc ann
