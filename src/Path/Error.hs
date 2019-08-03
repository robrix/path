{-# LANGUAGE FlexibleContexts #-}
module Path.Error where

import Control.Effect.Error
import Control.Effect.Reader
import Data.Foldable (toList)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Set as Set
import Path.Name
import Path.Pretty
import Path.Span

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
  where whichImports (name :~ excerpt) = prettyNotice (Notice Nothing excerpt (pretty "which imports" <+> squotes (pretty name) <> colon) [])
