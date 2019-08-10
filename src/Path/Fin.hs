{-# LANGUAGE DataKinds, EmptyCase, GADTs, StandaloneDeriving #-}
module Path.Fin where

import Path.Nat
import Path.Pretty

data Fin n where
  FZ :: Fin ('S n)
  FS :: Fin n -> Fin ('S n)

deriving instance Eq   (Fin n)
deriving instance Ord  (Fin n)
deriving instance Show (Fin n)

instance Pretty (Fin n) where
  pretty = prettyVar . finToInt

absurdFin :: Fin 'Z -> a
absurdFin v = case v of {}

finToInt :: Fin n -> Int
finToInt FZ     = 0
finToInt (FS n) = 1 + finToInt n

strengthenFin :: Fin ('S n) -> Maybe (Fin n)
strengthenFin FZ     = Nothing
strengthenFin (FS n) = Just n
