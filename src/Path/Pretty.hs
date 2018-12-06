module Path.Pretty where

import Control.Monad.IO.Class
import Data.Text.Lazy
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal hiding (putDoc)
import System.Console.Terminal.Size as Size
import System.IO (stdout)

prettyPrint :: (Pretty a, MonadIO m) => a -> m ()
prettyPrint = putDoc . pretty

putDoc :: MonadIO m => Doc AnsiStyle -> m ()
putDoc doc = do
  options <- layoutOptions
  liftIO (renderIO stdout (layoutPretty options (doc <> line)))

showDocIO :: MonadIO m => Doc AnsiStyle -> m String
showDocIO doc = do
  options <- layoutOptions
  pure (unpack (renderLazy (layoutPretty options doc)))

layoutOptions :: MonadIO m => m LayoutOptions
layoutOptions = do
  s <- maybe 80 Size.width <$> liftIO size
  pure LayoutOptions { layoutPageWidth = AvailablePerLine s 1 }


class PrettyPrec a where
  prettyPrec :: Int -> a -> Doc ann

prettyParens :: Bool -> Doc ann -> Doc ann
prettyParens True = parens
prettyParens False = id

prettyBraces :: Bool -> Doc ann -> Doc ann
prettyBraces True = braces
prettyBraces False = id
