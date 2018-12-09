module Path.Resources where

import Data.Function (on)
import qualified Data.Map as Map
import Path.FreeVariables
import Path.Name
import Path.Pretty
import Path.Usage
import Text.PrettyPrint.ANSI.Leijen

newtype Resources = Resources { unResources :: Map.Map Name Usage }
  deriving (Eq, Ord, Show)

empty :: Resources
empty = Resources Map.empty

singleton :: Name -> Usage -> Resources
singleton n = Resources . Map.singleton n

delete :: Name -> Resources -> Resources
delete n = Resources . Map.delete n . unResources

instance Pretty Resources where
  pretty = vsep . map (uncurry prettyBinding) . Map.toList . unResources
    where prettyBinding name u = pretty name <+> pretty "@" <+> pretty u

instance PrettyPrec Resources

instance FreeVariables Resources where
  fvs = fvs . unResources

instance Semigroup Resources where
  (<>) = fmap Resources . (Map.unionWith (<>) `on` unResources)
