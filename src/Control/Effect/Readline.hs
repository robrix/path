{-# LANGUAGE DeriveFunctor, DeriveGeneric, FlexibleContexts #-}
module Control.Effect.Readline
( -- * Readline effect
  Readline(..)
, prompt
, print
  -- * Line numbers
, Line(..)
, increment
) where

import Control.Carrier
import Data.Text.Prettyprint.Doc (Doc)
import Data.Text.Prettyprint.Doc.Render.Terminal (AnsiStyle)
import GHC.Generics (Generic1)
import Prelude hiding (print)

data Readline m k
  = Prompt String (Line -> Maybe String -> m k)
  | Print (Doc AnsiStyle) (m k)
  deriving (Functor, Generic1)

instance HFunctor Readline
instance Effect   Readline


prompt :: Has Readline sig m => String -> m (Line, Maybe String)
prompt p = send (Prompt p (curry pure))

print :: Has Readline sig m => Doc AnsiStyle -> m ()
print s = send (Print s (pure ()))


newtype Line = Line Int

increment :: Line -> Line
increment (Line n) = Line (n + 1)
