{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Path.Scope where

import Data.Coerce
import qualified Data.Map as Map
import Path.Context
import Path.Name
import Path.Pretty
import Path.Value

data Entry
  = Decl Type
  | Defn (Typed Value)
  deriving (Eq, Ord, Show)

instance Pretty Entry where
  pretty (Decl        ty)  =                             colon <+> pretty ty
  pretty (Defn (v ::: ty)) = pretty "=" <+> pretty v <+> colon <+> pretty ty

instance PrettyPrec Entry


newtype Scope = Scope { unScope :: Map.Map QName Entry }
  deriving (Eq, Monoid, Ord, Semigroup, Show)

union :: Scope -> Scope -> Scope
union = (<>)

filter :: (QName -> Entry -> Bool) -> Scope -> Scope
filter f = Scope . Map.filterWithKey f . unScope

under :: (Map.Map QName Entry -> Map.Map QName Entry) -> Scope -> Scope
under = coerce
