{-# LANGUAGE FlexibleContexts #-}
module Path.Pretty where

import Control.Monad.IO.Class
import qualified Data.Map as Map
import System.Console.Terminal.Size as Size
import System.IO (stdout)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>), putDoc)
import Text.Trifecta.Rendering (Span, render)

prettyPrint :: (MonadIO m, Pretty a) => a -> m ()
prettyPrint = putDoc . pretty

putDoc :: MonadIO m => Doc -> m ()
putDoc doc = do
  s <- maybe 80 Size.width <$> liftIO size
  liftIO (displayIO stdout (renderPretty 0.8 s (doc <> linebreak)))


class PrettyPrec a where
  prettyPrec :: Int -> a -> Doc

instance PrettyPrec Doc where
  prettyPrec _ = id

instance (PrettyPrec a, PrettyPrec b) => PrettyPrec (a, b) where
  prettyPrec _ (a, b) = tupled [ prettyPrec 0 a, prettyPrec 0 b ]

instance PrettyPrec Span where
  prettyPrec _ = pretty . render

instance PrettyPrec a => PrettyPrec [a] where
  prettyPrec _ = prettyList . map (prettyPrec 0)

instance (PrettyPrec k, PrettyPrec v) => PrettyPrec (Map.Map k v) where
  prettyPrec d = prettyPrec d . Map.toList

prettyParens :: Bool -> Doc -> Doc
prettyParens True = parens
prettyParens False = id

prettyBraces :: Bool -> Doc -> Doc
prettyBraces True = braces
prettyBraces False = id
