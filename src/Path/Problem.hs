module Path.Problem where

import Path.Name
import Path.Stack

data Problem a
  = Ex (Problem a) (Scope a)
  | Problem a ::: Problem a
  | Problem a :===: Problem a
  | Type
  | Lam (Problem a) (Scope a)
  | Pi (Problem a) (Scope a)
  | a :$ Stack (Problem a)

newtype Scope a = Scope (Problem (Incr a))
