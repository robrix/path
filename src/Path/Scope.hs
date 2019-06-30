{-# LANGUAGE GeneralizedNewtypeDeriving, TypeOperators #-}
module Path.Scope where

import Control.Arrow ((***))
import Data.Coerce
import qualified Data.Map as Map
import Path.Name
import Path.Pretty
import Path.Value

newtype Entry a = Entry { unEntry :: Maybe a ::: a }
  deriving (Eq, Ord, Show)

entryType :: Entry a -> a
entryType = typedType . unEntry

entryValue :: Entry a -> Maybe a
entryValue = typedTerm . unEntry

instance Pretty a => Pretty (Entry a) where
  pretty (Entry (Nothing ::: ty)) =         cyan colon <+> pretty ty
  pretty (Entry (Just v  ::: ty)) = align $ cyan colon <+> pretty ty <> hardline <> cyan (pretty "=") <+> pretty v


newtype Scope = Scope { unScope :: Map.Map Qualified (Entry (Type (Name Gensym))) }
  deriving (Eq, Monoid, Ord, Semigroup, Show)

lookup :: Qualified -> Scope -> Maybe (Entry (Type (Name Gensym)))
lookup q = Map.lookup q . unScope

null :: Scope -> Bool
null = Map.null . unScope

union :: Scope -> Scope -> Scope
union = (<>)

filter :: (Qualified -> Entry (Type (Name Gensym)) -> Bool) -> Scope -> Scope
filter = under . Map.filterWithKey

insert :: Qualified -> Entry (Type (Name Gensym)) -> Scope -> Scope
insert q = under . Map.insert q

under :: (Map.Map Qualified (Entry (Type (Name Gensym))) -> Map.Map Qualified (Entry (Type (Name Gensym)))) -> Scope -> Scope
under = coerce

instance Pretty Scope where
  pretty = tabulate2 space . map (green . pretty *** align . group . pretty) . Map.toList . unScope
