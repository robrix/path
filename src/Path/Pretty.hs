{-# LANGUAGE DefaultSignatures, FlexibleContexts #-}
module Path.Pretty where

import Control.Monad.IO.Class
import Data.Foldable (toList)
import qualified Data.Map as Map
import System.Console.Terminal.Size as Size
import System.IO (stdout)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>), putDoc)
import Text.Trifecta.Rendering (Span(..), render)
import Text.Trifecta.Result (ErrInfo(..))

prettyPrint :: (MonadIO m, PrettyPrec a) => a -> m ()
prettyPrint = putDoc . prettyPrec 0

prettys :: PrettyPrec a => a -> Doc
prettys = prettyPrec 0

putDoc :: MonadIO m => Doc -> m ()
putDoc doc = do
  s <- maybe 80 Size.width <$> liftIO size
  liftIO (displayIO stdout (renderPretty 0.8 s (doc <> linebreak)))

prettyErr :: Span -> Doc -> Maybe Doc -> Doc
prettyErr s msg ctx = nest 2 $ vsep
  ( group (prettyStart s <> colon <+> red (pretty "error") <> colon </> msg)
  : prettys s
  : toList ctx)

prettyStart :: Span -> Doc
prettyStart (Span start _ _) = pretty start


class PrettyPrec a where
  prettyPrec :: Int -> a -> Doc
  default prettyPrec :: Pretty a => Int -> a -> Doc
  prettyPrec _ = pretty

instance PrettyPrec Doc where
  prettyPrec _ = id

instance (PrettyPrec a, PrettyPrec b) => PrettyPrec (a, b) where
  prettyPrec _ (a, b) = tupled [ prettyPrec 0 a, prettyPrec 0 b ]

instance PrettyPrec () where
  prettyPrec _ = mempty

instance PrettyPrec Span where
  prettyPrec _ = pretty . render

instance PrettyPrec a => PrettyPrec [a] where
  prettyPrec _ = prettyList . map (prettyPrec 0)

instance (PrettyPrec k, PrettyPrec v) => PrettyPrec (Map.Map k v) where
  prettyPrec d = prettyPrec d . Map.toList

instance PrettyPrec ErrInfo where
  prettyPrec _ = pretty . _errDoc

prettyParens :: Bool -> Doc -> Doc
prettyParens True = parens
prettyParens False = id

prettyBraces :: Bool -> Doc -> Doc
prettyBraces True = braces
prettyBraces False = id
