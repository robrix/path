module Path.Env where

import qualified Data.Map as Map
import Path.Value

type Env = Map.Map String Value

lookup :: String -> Env -> Maybe Value
lookup n = Map.lookup n

insert :: String -> Value -> Env -> Env
insert n v = Map.insert n v
