{-# LANGUAGE TypeOperators #-}
module Path.Constraint where

import Path.Context
import Path.Name

data Constraint
  = Top
  | Constraint :/\: Constraint
  | Int :=: Int
  | Exists Int Constraint
  | Instance Name Int
  | Def Name Int Constraint
  | Let Name Int Constraint Constraint
  | Int :@ (Type QName)

data Witness = Witness
