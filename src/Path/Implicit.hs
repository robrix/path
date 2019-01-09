{-# LANGUAGE DeriveTraversable, FlexibleInstances, LambdaCase, MultiParamTypeClasses #-}
module Path.Implicit where

import qualified Data.Set as Set
import Path.Name

data Implicit v a
  = Hole v
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Ord v => FreeVariables1 v (Implicit v) where
  liftFvs _ = \case
    Hole v -> Set.singleton v
