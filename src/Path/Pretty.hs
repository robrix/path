module Path.Pretty
(
-- * Output
  prettyPrint
, putDoc
-- * Errors
, Level(..)
, Notice(..)
-- * Combinators
, prettyVar
, prettyMeta
, prettySpan
, tabulate2
, prettyParens
, prettyBraces
-- * Debugging
, tracePrettyM
-- * Pretty-printing with precedence
, Prec(..)
, prec
, atom
, withPrec
, module PP
) where

import Control.Arrow ((***))
import Control.Monad.IO.Class
import Data.Foldable (fold)
import Data.List (isSuffixOf)
import Path.Span
import System.Console.Terminal.Size as Size
import System.IO (stdout)
import System.IO.Unsafe
import Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>), bool, column, empty, putDoc)

prettyPrint :: (Pretty a, MonadIO m) => a -> m ()
prettyPrint = putDoc . pretty

putDoc :: MonadIO m => Doc -> m ()
putDoc doc = do
  s <- maybe 80 Size.width <$> liftIO size
  liftIO (displayIO stdout (renderPretty 0.8 s (doc <> linebreak)))

data Level
  = Warn
  | Error
  deriving (Eq, Ord, Show)

instance Pretty Level where
  pretty Warn  = magenta (pretty "warning")
  pretty Error = red (pretty "error")


data Notice = Notice
  { noticeLevel   :: Maybe Level
  , noticeExcerpt :: {-# UNPACK #-} !Excerpt
  , noticeReason  :: Doc
  , noticeContext :: [Doc]
  }
  deriving (Show)

instance Pretty Notice where
  pretty (Notice level (Excerpt path line span) reason context) = vsep
    ( nest 2 (group (vsep [bold (pretty path) <> colon <> bold (pretty (succ (posLine (spanStart span)))) <> colon <> bold (pretty (succ (posColumn (spanStart span)))) <> colon <> maybe mempty ((space <>) . (<> colon) . pretty) level, pretty reason]))
    : blue (pretty (succ (posLine (spanStart span)))) <+> align (fold
      [ blue (pretty '|') <+> pretty line <> if "\n" `isSuffixOf` line then mempty else blue (pretty "<EOF>") <> hardline
      , blue (pretty '|') <+> caret span
      ])
    : context)
    where caret span = pretty (replicate (posColumn (spanStart span)) ' ') <> prettySpan span


prettyVar :: Int -> Doc
prettyVar i = pretty (alphabet !! r : if q > 0 then show q else "")
  where (q, r) = i `divMod` 26
        alphabet = ['a'..'z']

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


prettyParens :: Bool -> Doc -> Doc
prettyParens True = parens
prettyParens False = id

prettyBraces :: Bool -> Doc -> Doc
prettyBraces True = braces
prettyBraces False = id


-- | Debugging helper.
tracePrettyM :: (Applicative m, Pretty a) => a -> m ()
tracePrettyM a = unsafePerformIO (pure () <$ prettyPrint a)


data Prec = Prec
  { precPrecedence :: Maybe Int
  , precDoc        :: Doc
  }
  deriving (Show)

prec :: Int -> Doc -> Prec
prec = Prec . Just

atom :: Doc -> Prec
atom = Prec Nothing

withPrec :: Int -> Prec -> Doc
withPrec d (Prec d' a) = prettyParens (maybe False (d >) d') a
