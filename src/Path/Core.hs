{-# LANGUAGE FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses #-}
module Path.Core where

import Data.Foldable (toList)
import qualified Data.Set as Set
import Path.Name
import Path.Plicity
import Path.Usage
import Text.Trifecta.Rendering (Span)

data Core
  = Free QName
  | Bound Int
  | Lam Name Scope
  | Core :$ Core
  | Type
  | Pi Name Plicity Usage Core (Scope)
  | Hole QName
  | Ann Span Core
  deriving (Eq, Ord, Show)

newtype Scope = Scope Core
  deriving (Eq, Ord, Show)

instance FreeVariables QName Core where
  fvs = \case
    Free v -> Set.singleton v
    Bound _ -> Set.empty
    Lam v (Scope b) -> Set.delete (Local v) (fvs b)
    f :$ a -> fvs f <> fvs a
    Type -> Set.empty
    Pi v _ _ t (Scope b) -> fvs t <> Set.delete (Local v) (fvs b)
    Hole v -> Set.singleton v
    Ann _ a -> fvs a

uses :: Name -> Core -> [Span]
uses n = go Nothing
  where go span = \case
          Free n'
            | Local n == n' -> toList span
            | otherwise     -> []
          Bound _ -> []
          Lam n' (Scope b)
            | n == n'   -> []
            | otherwise -> go span b
          f :$ a -> go span f <> go span a
          Type -> []
          Pi n' _ _ t (Scope b)
            | n == n'   -> go span t
            | otherwise -> go span t <> go span b
          Hole n'
            | Local n == n' -> toList span
            | otherwise     -> []
          Ann span a -> go (Just span) a
