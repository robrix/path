module Path.Parser.Mixfix where

import Data.List.NonEmpty (NonEmpty(..))

data Operator
  = Prefix (NonEmpty String)
  | Postfix (NonEmpty String)
  | Infix (NonEmpty String)
  | Closed String (NonEmpty String)
