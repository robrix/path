{-# LANGUAGE DeriveFunctor, DeriveGeneric #-}
module Path.Lexer where

import Control.Effect.Carrier
import GHC.Generics (Generic1)

data Lexer m k
  = Satisfy (Char -> Bool) (Char -> m k)
  deriving (Functor, Generic1)

instance HFunctor Lexer
instance Effect Lexer
