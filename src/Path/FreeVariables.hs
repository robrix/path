module Path.FreeVariables where

import Path.Name
import qualified Data.Set as Set

class FreeVariables t where
  fvs :: t -> Set.Set Name
