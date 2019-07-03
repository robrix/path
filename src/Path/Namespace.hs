{-# LANGUAGE DerivingVia, GeneralizedNewtypeDeriving, TypeOperators #-}
module Path.Namespace where

import Control.Arrow ((***))
import Data.Bitraversable
import Data.Coerce
import Data.Functor.Identity
import qualified Data.Map as Map
import Path.Core
import Path.Name
import Path.Pretty

newtype Entry a = Entry { unEntry :: Maybe a ::: a }
  deriving (Eq, Ord, Show)
  deriving (Foldable, Functor) via (Comp2 (:::) Maybe Identity)

instance Traversable Entry where
  traverse f  = fmap Entry . bitraverse (traverse f) f . unEntry

entryType :: Entry a -> a
entryType = typedType . unEntry

entryValue :: Entry a -> Maybe a
entryValue = typedTerm . unEntry

instance Pretty a => Pretty (Entry a) where
  pretty (Entry (Nothing ::: ty)) =         cyan colon <+> pretty ty
  pretty (Entry (Just v  ::: ty)) = align $ cyan colon <+> pretty ty <> hardline <> cyan (pretty "=") <+> pretty v


newtype Namespace = Namespace { unNamespace :: Map.Map Qualified (Entry (Core Qualified)) }
  deriving (Eq, Monoid, Ord, Semigroup, Show)

lookup :: Qualified -> Namespace -> Maybe (Entry (Core Qualified))
lookup q = Map.lookup q . unNamespace

null :: Namespace -> Bool
null = Map.null . unNamespace

union :: Namespace -> Namespace -> Namespace
union = (<>)

filter :: (Qualified -> Entry (Core Qualified) -> Bool) -> Namespace -> Namespace
filter = under . Map.filterWithKey

insert :: Qualified -> Entry (Core Qualified) -> Namespace -> Namespace
insert q = under . Map.insert q

under :: (Map.Map Qualified (Entry (Core Qualified)) -> Map.Map Qualified (Entry (Core Qualified))) -> Namespace -> Namespace
under = coerce

instance Pretty Namespace where
  pretty = tabulate2 space . map (green . pretty *** align . group . pretty) . Map.toList . unNamespace
