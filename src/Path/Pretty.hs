{-# LANGUAGE FlexibleContexts #-}
module Path.Pretty where

import Control.Effect
import Control.Effect.Reader
import Control.Monad.IO.Class
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>), putDoc)
import System.Console.Terminal.Size as Size
import System.IO (stdout)

prettyPrint :: (MonadIO m, Pretty a) => a -> m ()
prettyPrint = putDoc . pretty

putDoc :: MonadIO m => Doc -> m ()
putDoc doc = do
  s <- maybe 80 Size.width <$> liftIO size
  liftIO (displayIO stdout (renderPretty 0.8 s (doc <> linebreak)))

showDoc :: (Carrier sig m, Functor m, Member (Reader LayoutOptions) sig) => Doc -> m String
showDoc doc = asks (\ options -> displayS (layoutPretty options doc) "")

layoutOptions :: MonadIO m => m LayoutOptions
layoutOptions = do
  s <- maybe 80 Size.width <$> liftIO size
  pure LayoutOptions { layoutPageWidth = AvailablePerLine s 0.8 }

newtype LayoutOptions = LayoutOptions { layoutPageWidth :: PageWidth }
data PageWidth = AvailablePerLine Int Float

layoutPretty :: LayoutOptions -> Doc -> SimpleDoc
layoutPretty (LayoutOptions (AvailablePerLine w r)) = renderPretty r w

class PrettyPrec a where
  prettyPrec :: Int -> a -> Doc

prettyParens :: Bool -> Doc -> Doc
prettyParens True = parens
prettyParens False = id

prettyBraces :: Bool -> Doc -> Doc
prettyBraces True = braces
prettyBraces False = id
