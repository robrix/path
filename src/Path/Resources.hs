{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}
module Path.Resources where

import Data.Function (on)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Path.Name
import Path.Pretty
import Path.Semiring
import Path.Usage

newtype Resources = Resources { unResources :: Map.Map QName Usage }
  deriving (Eq, Ord, Show)

singleton :: QName -> Usage -> Resources
singleton n = Resources . Map.singleton n

lookup :: QName -> Resources -> Usage
lookup n = fromMaybe zero . Map.lookup n . unResources

delete :: QName -> Resources -> Resources
delete n = Resources . Map.delete n . unResources

mult :: Usage -> Resources -> Resources
mult = (><<)

instance Pretty Resources where
  pretty = vsep . map (uncurry prettyBinding) . Map.toList . unResources
    where prettyBinding name u = pretty name <+> pretty "@" <+> prettyPrec 0 u

instance PrettyPrec Resources

instance Semigroup Resources where
  (<>) = fmap Resources . (Map.unionWith (<>) `on` unResources)

instance Monoid Resources where
  mempty = Resources Map.empty

instance Semiring Resources where
  (><) = fmap Resources . (Map.intersectionWith (><) `on` unResources)

instance LeftModule Usage Resources where
  u ><< Resources r = Resources (fmap (u ><) r)

instance FreeVariables QName Resources where
  fvs = fvs . unResources
