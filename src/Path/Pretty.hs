{-# LANGUAGE DefaultSignatures, FlexibleContexts #-}
module Path.Pretty
( PrettyPrec(..)
, prettyPrint
, prettys
, putDoc
, prettyNotice
, prettyErr
, prettyWarn
, prettyInfo
, prettyStart
, prettyVar
, prettyParens
, prettyBraces
, tabulate2
, module PP
) where

import Control.Arrow ((***))
import Control.Monad.IO.Class
import qualified Data.Map as Map
import System.Console.Terminal.Size as Size
import System.IO (stdout)
import Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>), bool, column, empty, putDoc)
import Text.Trifecta.Rendering (Rendering(..), Span(..), render)
import Text.Trifecta.Result (ErrInfo(..))

prettyPrint :: (MonadIO m, PrettyPrec a) => a -> m ()
prettyPrint = putDoc . prettyPrec 0

prettys :: PrettyPrec a => a -> Doc
prettys = prettyPrec 0

putDoc :: MonadIO m => Doc -> m ()
putDoc doc = do
  s <- maybe 80 Size.width <$> liftIO size
  liftIO (displayIO stdout (renderPretty 0.8 s (doc <> linebreak)))

prettyNotice :: Span -> Maybe Doc -> Doc -> [Doc] -> Doc
prettyNotice s lvl msg ctx = vsep
  ( nest 2 (group (prettyStart s <> colon <> maybe mempty ((space <>) . (<> colon)) lvl </> msg))
  : prettys s
  : ctx)

prettyErr :: Span -> Doc -> [Doc] -> Doc
prettyErr s = prettyNotice s (Just (red (pretty "error")))

prettyWarn :: Span -> Doc -> [Doc] -> Doc
prettyWarn s = prettyNotice s (Just (magenta (pretty "warning")))

prettyInfo :: Span -> Doc -> [Doc] -> Doc
prettyInfo s = prettyNotice s Nothing

prettyStart :: Span -> Doc
prettyStart (Span start _ _) = pretty start

prettyVar :: Int -> Doc
prettyVar i = pretty (alphabet !! r : if q > 0 then show q else "")
    where (q, r) = i `divMod` 26
          alphabet = ['a'..'z']

tabulate2 :: (Pretty a, Pretty b) => Doc -> [(a, b)] -> Doc
tabulate2 _ [] = mempty
tabulate2 s cs = vsep (map (uncurry entry) cs')
  where entry a b = fill w (pretty a) <> s <> pretty b
        w = maximum (map (columnWidth . fst) cs')
        cs' = map (column *** pretty) cs

newtype Column = Column { unColumn :: (Int, Doc) }

column :: Pretty a => a -> Column
column a = Column (length (show (plain a')), a')
  where a' = pretty a

columnWidth :: Column -> Int
columnWidth = fst . unColumn

instance Pretty Column where
  pretty = snd . unColumn


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

instance PrettyPrec Rendering

prettyParens :: Bool -> Doc -> Doc
prettyParens True = parens
prettyParens False = id

prettyBraces :: Bool -> Doc -> Doc
prettyBraces True = braces
prettyBraces False = id
