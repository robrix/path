{-# LANGUAGE GeneralizedNewtypeDeriving, TypeOperators #-}
module Path.Scope where

import Control.Arrow ((***))
import Data.Coerce
import qualified Data.Map as Map
import Path.Name
import Path.Pretty
import Path.Value hiding (Scope(..))

data Entry
  = Decl Type
  | Defn (Value ::: Type)
  deriving (Eq, Ord, Show)

entryType :: Entry -> Type
entryType (Decl        ty)  = ty
entryType (Defn (_ ::: ty)) = ty

entryValue :: Entry -> Maybe Value
entryValue (Defn (v ::: _)) = Just v
entryValue _                = Nothing

instance Pretty Entry where
  pretty (Decl        ty)  =         colon <+> pretty ty
  pretty (Defn (v ::: ty)) = align $ colon <+> pretty ty </> pretty "=" <+> pretty v

instance PrettyPrec Entry


newtype Scope = Scope { unScope :: Map.Map QName Entry }
  deriving (Eq, Monoid, Ord, Semigroup, Show)

lookup :: QName -> Scope -> Maybe Entry
lookup q = Map.lookup q . unScope

null :: Scope -> Bool
null = Map.null . unScope

union :: Scope -> Scope -> Scope
union = (<>)

filter :: (QName -> Entry -> Bool) -> Scope -> Scope
filter = under . Map.filterWithKey

insert :: QName -> Entry -> Scope -> Scope
insert q = under . Map.insert q

under :: (Map.Map QName Entry -> Map.Map QName Entry) -> Scope -> Scope
under = coerce

instance Pretty Scope where
  pretty = tabulate2 space . map (green . pretty *** align . group . pretty) . Map.toList . unScope

instance PrettyPrec Scope
