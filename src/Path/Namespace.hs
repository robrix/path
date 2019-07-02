{-# LANGUAGE GeneralizedNewtypeDeriving, TypeOperators #-}
module Path.Namespace where

import Control.Arrow ((***))
import Data.Coerce
import qualified Data.Map as Map
import Path.Core
import Path.Name
import Path.Pretty

newtype Entry a = Entry { unEntry :: Maybe a ::: a }
  deriving (Eq, Ord, Show)

entryType :: Entry a -> a
entryType = typedType . unEntry

entryValue :: Entry a -> Maybe a
entryValue = typedTerm . unEntry

instance Pretty a => Pretty (Entry a) where
  pretty (Entry (Nothing ::: ty)) =         cyan colon <+> pretty ty
  pretty (Entry (Just v  ::: ty)) = align $ cyan colon <+> pretty ty <> hardline <> cyan (pretty "=") <+> pretty v


newtype Namespace = Namespace { unNamespace :: Map.Map Qualified (Entry (Type Qualified)) }
  deriving (Eq, Monoid, Ord, Semigroup, Show)

lookup :: Qualified -> Namespace -> Maybe (Entry (Type Qualified))
lookup q = Map.lookup q . unNamespace

null :: Namespace -> Bool
null = Map.null . unNamespace

union :: Namespace -> Namespace -> Namespace
union = (<>)

filter :: (Qualified -> Entry (Type Qualified) -> Bool) -> Namespace -> Namespace
filter = under . Map.filterWithKey

insert :: Qualified -> Entry (Type Qualified) -> Namespace -> Namespace
insert q = under . Map.insert q

under :: (Map.Map Qualified (Entry (Type Qualified)) -> Map.Map Qualified (Entry (Type Qualified))) -> Namespace -> Namespace
under = coerce

instance Pretty Namespace where
  pretty = tabulate2 space . map (green . pretty *** align . group . pretty) . Map.toList . unNamespace
