{-# LANGUAGE GeneralizedNewtypeDeriving, TypeOperators #-}
module Path.Scope where

import Control.Arrow ((***))
import Data.Coerce
import qualified Data.Map as Map
import Path.Name
import Path.Pretty
import Path.Value hiding (Scope(..))

newtype Entry = Entry { unEntry :: Maybe (Value Name) ::: Type Name }
  deriving (Eq, Ord, Show)

entryType :: Entry -> Type Name
entryType = typedType . unEntry

entryValue :: Entry -> Maybe (Value Name)
entryValue = typedTerm . unEntry

instance Pretty Entry where
  pretty (Entry (Nothing ::: ty)) =         cyan colon <+> pretty ty
  pretty (Entry (Just v  ::: ty)) = align $ cyan colon <+> pretty ty <> hardline <> cyan (pretty "=") <+> pretty v


newtype Scope = Scope { unScope :: Map.Map Qualified Entry }
  deriving (Eq, Monoid, Ord, Semigroup, Show)

lookup :: Qualified -> Scope -> Maybe Entry
lookup q = Map.lookup q . unScope

null :: Scope -> Bool
null = Map.null . unScope

union :: Scope -> Scope -> Scope
union = (<>)

filter :: (Qualified -> Entry -> Bool) -> Scope -> Scope
filter = under . Map.filterWithKey

insert :: Qualified -> Entry -> Scope -> Scope
insert q = under . Map.insert q

under :: (Map.Map Qualified Entry -> Map.Map Qualified Entry) -> Scope -> Scope
under = coerce

instance Pretty Scope where
  pretty = tabulate2 space . map (green . pretty *** align . group . pretty) . Map.toList . unScope
