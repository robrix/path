module Path.Surface where

import Path.Name
import Path.Plicity
import Path.Usage
import Text.Trifecta.Rendering (Span)

data Surface
  = Free UName
  | Lam (Maybe UName) Surface
  | Surface :$ Surface
  | Type
  | Pi (Maybe UName) Plicity Usage Surface Surface
  | Hole UName
  | (Usage, Surface) :-> Surface
  | Ann Span Surface
  deriving (Eq, Ord, Show)
