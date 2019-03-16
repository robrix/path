{-# LANGUAGE FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TypeOperators #-}
module Path.Core where

import Data.Foldable (toList)
import Path.Name
import Path.Plicity
import Path.Usage
import Prelude hiding (pi)
import Text.Trifecta.Rendering (Span)

data Core
  = Var (Name Local)
  | Lam (Maybe User) Core
  | Core :$ Core
  | Type
  | Pi (Maybe User) Plicity Usage Core Core
  | Hole User
  | Ann Span Core
  deriving (Eq, Ord, Show)


uses :: Name Local -> Core -> [Span]
uses n = go Nothing
  where go span = \case
          Var n'
            | n == n'   -> toList span
            | otherwise -> []
          Lam (Just n') _
            | n == Local (User n') -> []
          Lam _ b-> go span b
          f :$ a -> go span f <> go span a
          Type -> []
          Pi (Just n') _ _ t _
            | n == Local (User n') -> go span t
          Pi _ _ _ t b -> go span t <> go span b
          Hole n'
            | n == Local (User n') -> toList span
            | otherwise            -> []
          Ann span a -> go (Just span) a
