module Path.Scope where

import Path.Context
import Path.Name
import Path.Value

data Entry
  = QName := Typed Value
