module Path.Span
( Span(..)
, Spanned(..)
, unSpanned
, runSpanned
) where

import Control.Effect
import Control.Effect.Reader
import Text.Trifecta.Rendering (Span (..), Spanned (..))

unSpanned :: Spanned a -> a
unSpanned (a :~ _) = a

runSpanned :: Carrier sig m => (a -> ReaderC Span m b) -> Spanned a -> m (Spanned b)
runSpanned f v@(_ :~ s) = runReader s (traverse f v)
