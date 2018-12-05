{-# LANGUAGE FlexibleInstances #-}
module Path.FreeVariables where

import Path.Name
import qualified Data.Set as Set

class FreeVariables t where
  fvs :: t -> Set.Set Name

instance FreeVariables (Set.Set Name) where
  fvs = id
