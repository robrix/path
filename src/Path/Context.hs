module Path.Context where

import qualified Data.Map as Map
import Path.Eval
import Path.Name

type Context = Map.Map Name Value
