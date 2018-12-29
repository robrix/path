{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}
module Path.Resources where

import Data.Function (on)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Path.Name
import Path.Pretty
import Path.Semiring

newtype Resources r = Resources { unResources :: Map.Map QName r }
  deriving (Eq, Ord, Show)

singleton :: QName -> r -> Resources r
singleton n = Resources . Map.singleton n

lookup :: Monoid r => QName -> Resources r -> r
lookup n = fromMaybe zero . Map.lookup n . unResources

delete :: QName -> Resources r -> Resources r
delete n = Resources . Map.delete n . unResources

instance PrettyPrec r => Pretty (Resources r) where
  pretty = vsep . map (uncurry prettyBinding) . Map.toList . unResources
    where prettyBinding name u = pretty name <+> pretty "@" <+> prettyPrec 0 u

instance PrettyPrec r => PrettyPrec (Resources r)

instance Semigroup r => Semigroup (Resources r) where
  (<>) = fmap Resources . (Map.unionWith (<>) `on` unResources)

instance Semigroup r => Monoid (Resources r) where
  mempty = Resources Map.empty

instance Semiring r => Semiring (Resources r) where
  (><) = fmap Resources . (Map.intersectionWith (><) `on` unResources)

instance Semiring r => LeftModule r (Resources r) where
  u ><< Resources r = Resources (fmap (u ><) r)

instance FreeVariables QName r => FreeVariables QName (Resources r) where
  fvs = fvs . unResources
