{-# LANGUAGE FlexibleContexts #-}
module Path.Error where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader
import Path.Name
import Path.Pretty
import Text.Trifecta.Rendering (Span)

data ElabError = ElabError
  { errorSpan    :: Span
  , errorReason  :: ErrorReason
  }
  deriving (Eq, Ord, Show)

data ErrorReason
  = FreeVariable Name
  deriving (Eq, Ord, Show)

instance Pretty ElabError where
  pretty (ElabError span reason) = case reason of
    FreeVariable name -> prettyErr span (pretty "free variable" <+> squotes (pretty name)) []

instance PrettyPrec ElabError

freeVariable :: (Carrier sig m, Member (Error Doc) sig, Member (Reader Span) sig, Pretty name) => name -> m a
freeVariable name = do
  span <- ask
  throwError (prettyErr span (pretty "free variable" <+> squotes (pretty name)) [])
