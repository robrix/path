module Path.Resources where

import qualified Data.Map as Map
import Path.Name
import Path.Usage

type Resources = Map.Map Name Usage

empty :: Resources
empty = Map.empty

singleton :: Name -> Usage -> Resources
singleton n = Map.singleton n

delete :: Name -> Resources -> Resources
delete n = Map.delete n
