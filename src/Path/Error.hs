{-# LANGUAGE TypeOperators #-}
module Path.Error where

import Path.Context as Context
import Path.Name
import Path.Pretty
import Path.Value
import Text.Trifecta.Rendering (Span)

data ElabError = ElabError
  { errorSpan    :: Span
  , errorContext :: Context (Type Meta)
  , errorReason  :: ErrorReason
  }
  deriving (Eq, Ord, Show)

data ErrorReason
  = FreeVariable Name
  deriving (Eq, Ord, Show)

instance Pretty ElabError where
  pretty (ElabError span _ reason) = case reason of
    FreeVariable name -> prettyErr span (pretty "free variable" <+> squotes (pretty name)) []

instance PrettyPrec ElabError
