{-# LANGUAGE DeriveTraversable #-}
module Path.Pretty
( prettyPrint
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
, tracePrettyM
, Prec(..)
, prettyPrec
, prec
, atom
, module PP
) where

import Control.Arrow ((***))
import Control.Monad.IO.Class
import Path.Span
import System.Console.Terminal.Size as Size
import System.IO (stdout)
import System.IO.Unsafe
import Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>), bool, column, empty, putDoc)
import Text.Trifecta.Rendering (render)

prettyPrint :: (Pretty a, MonadIO m) => a -> m ()
prettyPrint = putDoc . pretty

putDoc :: MonadIO m => Doc -> m ()
putDoc doc = do
  s <- maybe 80 Size.width <$> liftIO size
  liftIO (displayIO stdout (renderPretty 0.8 s (doc <> linebreak)))

data Level
  = Error
  | Warn
  deriving (Eq, Ord, Show)

instance Pretty Level where
  pretty Error = red (pretty "error")
  pretty Warn  = magenta (pretty "warning")

prettyNotice :: Maybe Level -> Span -> Doc -> [Doc] -> Doc
prettyNotice lvl s msg ctx = vsep
  ( nest 2 (group (prettyStart s <> colon <> maybe mempty ((space <>) . (<> colon) . pretty) lvl </> msg))
  : pretty (render s)
  : ctx)

prettyErr :: Span -> Doc -> [Doc] -> Doc
prettyErr = prettyNotice (Just Error)

prettyWarn :: Span -> Doc -> [Doc] -> Doc
prettyWarn = prettyNotice (Just Warn)

prettyInfo :: Span -> Doc -> [Doc] -> Doc
prettyInfo = prettyNotice Nothing

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


prettyParens :: Bool -> Doc -> Doc
prettyParens True = parens
prettyParens False = id

prettyBraces :: Bool -> Doc -> Doc
prettyBraces True = braces
prettyBraces False = id


-- | Debugging helper.
tracePrettyM :: (Applicative m, Pretty a) => a -> m ()
tracePrettyM a = unsafePerformIO (pure () <$ prettyPrint a)


data Prec a = Prec
  { precPrecedence :: Maybe Int
  , precDoc        :: a
  }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Pretty a => Pretty (Prec a) where
  pretty = pretty . precDoc

prec :: Int -> a -> Prec a
prec = Prec . Just

atom :: a -> Prec a
atom = Prec Nothing

prettyPrec :: Int -> Prec Doc -> Doc
prettyPrec d (Prec d' a) = prettyParens (maybe False (d >) d') a
