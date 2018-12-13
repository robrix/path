{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module Path.Resources where

import Data.Function (on)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Path.Pretty
import Path.Semiring
import Text.PrettyPrint.ANSI.Leijen

newtype Resources v r = Resources { unResources :: Map.Map v r }
  deriving (Eq, Ord, Show)

empty :: Resources v r
empty = Resources Map.empty

singleton :: v -> r -> Resources v r
singleton n = Resources . Map.singleton n

lookup :: (Monoid r, Ord v) => v -> Resources v r -> r
lookup n = fromMaybe zero . Map.lookup n . unResources

delete :: Ord v => v -> Resources v r -> Resources v r
delete n = Resources . Map.delete n . unResources

instance (Pretty v, PrettyPrec r) => Pretty (Resources v r) where
  pretty = vsep . map (uncurry prettyBinding) . Map.toList . unResources
    where prettyBinding name u = pretty name <+> pretty "@" <+> prettyPrec 0 u

instance (Pretty v, PrettyPrec r) => PrettyPrec (Resources v r)

instance (Semigroup r, Ord v) => Semigroup (Resources v r) where
  (<>) = fmap Resources . (Map.unionWith (<>) `on` unResources)

instance (Semigroup r, Ord v) => Monoid (Resources v r) where
  mempty = Resources Map.empty

instance (Semiring r, Ord v) => Semiring (Resources v r) where
  (><) = fmap Resources . (Map.intersectionWith (><) `on` unResources)

instance Semiring r => LeftModule r (Resources v r) where
  u ><< Resources r = Resources (fmap (u ><) r)
