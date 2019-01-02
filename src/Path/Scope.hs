module Path.Scope where

import Path.Context
import Path.Value

data Entry
  = Decl Type
  | Defn (Typed Value)
