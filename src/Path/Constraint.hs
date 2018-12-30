{-# LANGUAGE TypeOperators #-}
module Path.Constraint where

import Path.Context
import Path.Name

data Constraint
  = Top
  | Constraint :/\: Constraint
  | Exists Int Constraint
  | Type QName :=: Type QName
  | Let Int Int Constraint Constraint
  | Int :@ (Type QName)
