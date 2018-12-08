{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Path.Context where

import qualified Data.Map as Map
import Path.Eval
import Path.Name
import Text.PrettyPrint.ANSI.Leijen

type Type = Value

newtype Context = Context { unContext :: Map.Map Name Type }
  deriving (Eq, Monoid, Ord, Semigroup, Show)

empty :: Context
empty = Context Map.empty

lookup :: Name -> Context -> Maybe Type
lookup n = Map.lookup n . unContext

insert :: Name -> Type -> Context -> Context
insert n v = Context . Map.insert n v . unContext

instance Pretty Context where
  pretty = vsep . map prettyBinding . Map.toList . unContext
    where prettyBinding (name, ty) = pretty name <+> pretty ":" <+> group (pretty ty)
