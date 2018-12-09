{-# LANGUAGE FlexibleInstances #-}
module Path.FreeVariables where

import Path.Name
import Path.Usage
import qualified Data.Set as Set
import Text.Trifecta.Rendering (Span)

class FreeVariables t where
  fvs :: t -> Set.Set Name

instance FreeVariables (Set.Set Name) where
  fvs = id

instance FreeVariables Span where
  fvs _ = mempty

instance (FreeVariables a, FreeVariables b) => FreeVariables (a, b) where
  fvs (a, b) = fvs a <> fvs b

instance FreeVariables a => FreeVariables [a] where
  fvs = foldMap fvs

instance FreeVariables Name where
  fvs = Set.singleton

instance FreeVariables Usage where
  fvs _ = mempty


class FreeVariables1 t where
  liftFvs :: (a -> Set.Set Name) -> t a -> Set.Set Name

fvs1 :: (FreeVariables1 t, FreeVariables a) => t a -> Set.Set Name
fvs1 = liftFvs fvs
