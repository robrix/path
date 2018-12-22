module Path.Parser.Mixfix where

import Data.List.NonEmpty (NonEmpty(..))

data Operator
  = Prefix (NonEmpty String)
  | Postfix (NonEmpty String)
  | Infix (NonEmpty String)
  | Closed String (NonEmpty String)

betweenOp :: String -> String -> Operator
betweenOp a b = Closed a (b :| [])

parensOp :: Operator
parensOp = betweenOp "(" ")"

ifthenelse :: Operator
ifthenelse = Prefix ("if" :| [ "then", "else" ])
