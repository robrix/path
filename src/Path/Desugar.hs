{-# LANGUAGE FlexibleContexts, TypeOperators #-}
module Path.Desugar where

import Path.Core as Core
import Path.Name
import Path.Plicity
import qualified Path.Surface as Surface
import Path.Term

desugar :: Term (Surface.Surface (Maybe UName) UName) a
        -> Term (Core (Maybe UName) UName) a
desugar = cata go
  where go out span = flip In span $ case out of
          Surface.Free v -> Core.Free v
          Surface.Lam n b -> Core.Lam n (Scope b)
          f Surface.:$ a -> f Core.:$ a
          Surface.Type -> Core.Type
          Surface.Pi n p u t b -> Core.Pi n p u t (Scope b)
          Surface.Hole v -> Core.Hole v
          (u, a) Surface.:-> b -> Core.Pi Nothing Ex u a (Scope b)
