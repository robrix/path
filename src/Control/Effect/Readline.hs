{-# LANGUAGE DeriveFunctor, DeriveGeneric, FlexibleContexts #-}
module Control.Effect.Readline
( -- * Readline effect
  Readline(..)
, prompt
, print
  -- * Line numbers
, Line(..)
, increment
, linePos
) where

import Control.Effect.Carrier
import Data.Text.Prettyprint.Doc (Doc)
import Data.Text.Prettyprint.Doc.Render.Terminal (AnsiStyle)
import GHC.Generics (Generic1)
import Path.Span
import Prelude hiding (print)

data Readline m k
  = Prompt String (Line -> Maybe String -> m k)
  | Print (Doc AnsiStyle) (m k)
  deriving (Functor, Generic1)

instance HFunctor Readline
instance Effect   Readline


prompt :: (Carrier sig m, Member Readline sig) => String -> m (Line, Maybe String)
prompt p = send (Prompt p (curry pure))

print :: (Carrier sig m, Member Readline sig) => Doc AnsiStyle -> m ()
print s = send (Print s (pure ()))


newtype Line = Line Int

increment :: Line -> Line
increment (Line n) = Line (n + 1)

linePos :: Line -> Pos
linePos (Line l) = Pos l 0
