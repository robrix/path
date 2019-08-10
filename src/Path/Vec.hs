{-# LANGUAGE DataKinds, DeriveTraversable, GADTs, StandaloneDeriving #-}
module Path.Vec where

import Path.Fin
import Path.Nat

data Vec n a where
  VZ :: Vec 'Z a
  (:#) :: a -> Vec n a -> Vec ('S n) a

infixr 5 :#

deriving instance Eq   a => Eq   (Vec n a)
deriving instance Ord  a => Ord  (Vec n a)
deriving instance Show a => Show (Vec n a)

deriving instance Foldable    (Vec n)
deriving instance Functor     (Vec n)
deriving instance Traversable (Vec n)

(!) :: Vec n a -> Fin n -> a
(h :# _) ! FZ   = h
(_ :# t) ! FS n = t ! n
VZ       ! n    = absurdFin n

infixl 9 !
