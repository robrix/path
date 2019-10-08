{-# LANGUAGE DefaultSignatures, FlexibleInstances, LambdaCase, QuantifiedConstraints, RankNTypes, ScopedTypeVariables #-}
module Path.Pretty
(
-- * Styled pretty-printing class
  Doc
, Pretty(..)
-- * Output
, prettyPrint
, putDoc
-- * Combinators
, prettyVar
, prettyMeta
, prettySpan
, tabulate2
, prettyParens
, prettyBraces
-- * Foreground colours
, red
, yellow
, green
, cyan
, blue
, magenta
-- * Foreground colours (dull)
, dullblack
-- * Styling
, bold
, plain
-- * Debugging
, tracePrettyM
-- * Pretty-printing with precedence
, Prec(..)
, prec
, atom
, withPrec
, module PP
  -- * Pretty-printing terms
, prettyTerm
, prettyTermInContext
) where

import Control.Arrow ((***))
import Control.Monad.IO.Class
import Path.Span
import Path.Fin
import Path.Vec
import Syntax.Module
import Syntax.Pretty
import Syntax.Term
import Syntax.Var
import System.Console.Terminal.Size as Size
import System.IO (stdout)
import System.IO.Unsafe
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc as PP hiding (Doc, Pretty (..), column)
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Text.Prettyprint.Doc.Internal (unsafeTextWithoutNewlines)
import Data.Text.Prettyprint.Doc.Render.Terminal (AnsiStyle, Color (..), color, colorDull)
import qualified Data.Text.Prettyprint.Doc.Render.Terminal as ANSI

type Doc = PP.Doc AnsiStyle

class Pretty a where
  pretty :: a -> Doc
  default pretty :: PP.Pretty a => a -> Doc
  pretty = PP.pretty

  prettyList :: [a] -> Doc
  prettyList = align . list . map pretty

instance Pretty Char where
  prettyList = pretty . Text.pack

instance Pretty Text.Text where pretty = vsep . map unsafeTextWithoutNewlines . Text.splitOn (Text.pack "\n")
instance Pretty (PP.Doc AnsiStyle) where pretty = id
instance Pretty Int
instance Pretty a => Pretty [a] where
  pretty = prettyList

prettyPrint :: (Pretty a, MonadIO m) => a -> m ()
prettyPrint = putDoc . pretty

putDoc :: MonadIO m => Doc -> m ()
putDoc doc = do
  s <- maybe 80 Size.width <$> liftIO size
  liftIO (ANSI.renderIO stdout (layoutSmart defaultLayoutOptions { layoutPageWidth = AvailablePerLine s 0.8 } (doc <> line)))


prettyMeta :: Pretty a => a -> Doc
prettyMeta n = dullblack (bold (pretty '?' <> pretty n))


prettySpan :: Span -> Doc
prettySpan (Span start end)
  | start == end                 = green (pretty '^')
  | posLine start == posLine end = green (pretty (replicate (posColumn end - posColumn start) '~'))
  | otherwise                    = green (pretty "^…")


tabulate2 :: (Pretty a, Pretty b) => Doc -> [(a, b)] -> Doc
tabulate2 _ [] = mempty
tabulate2 s cs = vsep (map (uncurry entry) cs')
  where entry a b = fill w (pretty a) <> s <> b
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


prettyBraces :: Bool -> PP.Doc ann -> PP.Doc ann
prettyBraces True  = braces
prettyBraces False = id


red, yellow, green, cyan, blue, magenta :: Doc -> Doc
red     = annotate $ color Red
yellow  = annotate $ color Yellow
green   = annotate $ color Green
cyan    = annotate $ color Cyan
blue    = annotate $ color Blue
magenta = annotate $ color Magenta

dullblack :: Doc -> Doc
dullblack = annotate $ colorDull Black

bold, plain :: Doc -> Doc
bold = annotate ANSI.bold
plain = unAnnotate


-- | Debugging helper.
tracePrettyM :: (Applicative m, Pretty a) => a -> m ()
tracePrettyM a = unsafePerformIO (pure () <$ prettyPrint a)


prettyTerm
  :: forall sig a
  .  (forall g . Foldable g => Foldable (sig g), Pretty a, RightModule sig)
  => (forall f n . (Foldable f, Monad f) => (forall n . Vec n Doc -> f (Var (Fin n) a) -> Prec Doc) -> Vec n Doc -> sig f (Var (Fin n) a) -> Prec Doc)
  -> Term sig a
  -> Doc
prettyTerm alg = unPrec . prettyTermInContext pretty alg VZ . fmap F

prettyTermInContext
  :: forall sig n a doc
  .  (forall g . Foldable g => Foldable (sig g), RightModule sig)
  => (a -> doc)
  -> (forall f n . (Foldable f, Monad f) => (forall n . Vec n doc -> f (Var (Fin n) a) -> Prec doc) -> Vec n doc -> sig f (Var (Fin n) a) -> Prec doc)
  -> Vec n doc
  -> Term sig (Var (Fin n) a)
  -> Prec doc
prettyTermInContext var alg = go where
  go :: forall n . Vec n doc -> Term sig (Var (Fin n) a) -> Prec doc
  go ctx = \case
    Var v -> atom (unVar (ctx !) var v)
    Alg t -> alg go ctx t
