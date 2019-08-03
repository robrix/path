{-# LANGUAGE FlexibleContexts #-}
module Path.Error where

import Control.Effect.Error
import Control.Effect.Reader
import Data.Foldable (fold, toList)
import Data.List (isSuffixOf)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Set as Set
import Path.Name
import Path.Pretty
import Path.Span

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
    ( nest 2 (group (vsep [bold (pretty path) <> colon <> bold (pretty (succ (posLine (spanStart span)))) <> colon <> bold (pretty (succ (posColumn (spanStart span)))) <> colon <> maybe mempty ((space <>) . (<> colon) . pretty) level, reason]))
    : blue (pretty (succ (posLine (spanStart span)))) <+> align (fold
      [ blue (pretty '|') <+> pretty line <> if "\n" `isSuffixOf` line then mempty else blue (pretty "<EOF>") <> hardline
      , blue (pretty '|') <+> caret span
      ])
    : context)
    where caret span = pretty (replicate (posColumn (spanStart span)) ' ') <> prettySpan span


freeVariables :: (Carrier sig m, Member (Error Notice) sig, Member (Reader Excerpt) sig, Ord name, Pretty name) => NonEmpty name -> m a
freeVariables names = do
  span <- ask
  throwError (Notice (Just Error) span (pretty "free variable" <> (if length names == 1 then mempty else pretty "s") <+> fillSep (punctuate comma (map pretty (toList (foldMap Set.singleton names))))) [])

ambiguousName :: (Carrier sig m, Member (Error Notice) sig, Member (Reader Excerpt) sig) => User -> NonEmpty Qualified -> m a
ambiguousName name sources = do
  span <- ask
  throwError $ Notice (Just Error) span (pretty "ambiguous name" <+> squotes (pretty name)) [nest 2 (vsep
    ( pretty "it could refer to"
    : map pretty (toList sources)))]


unknownModule :: (Carrier sig m, Member (Error Notice) sig) => Spanned ModuleName -> m a
unknownModule (name :~ excerpt) = throwError (Notice (Just Error) excerpt (pretty "Could not find module" <+> squotes (pretty name)) [])

cyclicImport :: (Carrier sig m, Member (Error Notice) sig) => NonEmpty (Spanned ModuleName) -> m a
cyclicImport (name :~ span :| [])    = throwError (Notice (Just Error) span (pretty "Cyclic import of" <+> squotes (pretty name)) [])
cyclicImport (name :~ span :| names) = throwError (Notice (Just Error) span (pretty "Cyclic import of" <+> squotes (pretty name) <> colon) (foldr ((:) . whichImports) [ whichImports (name :~ span) ] names))
  where whichImports (name :~ excerpt) = pretty (Notice Nothing excerpt (pretty "which imports" <+> squotes (pretty name) <> colon) [])
