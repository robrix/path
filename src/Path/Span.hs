module Path.Span
( Span(..)
, Spanned(..)
, runSpanned
) where

import Control.Effect
import Control.Effect.Reader
import Text.Trifecta.Rendering (Span (..), Spanned (..))

runSpanned :: Carrier sig m => (a -> ReaderC Span m b) -> Spanned a -> m (Spanned b)
runSpanned f v@(_ :~ s) = runReader s (traverse f v)
