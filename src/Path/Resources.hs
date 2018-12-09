module Path.Resources where

import qualified Data.Map as Map
import Path.Name
import Path.Usage

type Resources = Map.Map Name Usage

delete :: Name -> Resources -> Resources
delete n = Map.delete n
