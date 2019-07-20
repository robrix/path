{-# LANGUAGE DeriveFunctor, DeriveGeneric #-}
module Path.Lexer where

import GHC.Generics (Generic1)

data Lexer m k
  = Satisfy (Char -> Bool) (Bool -> m k)
  deriving (Functor, Generic1)
