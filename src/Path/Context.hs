module Path.Context where

import qualified Data.Map as Map
import Path.Eval
import Path.Name

type Context = Map.Map Name Value

lookup :: Name -> Context -> Maybe Value
lookup n = Map.lookup n

insert :: Name -> Value -> Context -> Context
insert n v = Map.insert n v
