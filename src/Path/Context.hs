{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Path.Context where

import qualified Data.Map as Map
import Path.Eval
import Path.Name
import Text.PrettyPrint.ANSI.Leijen

newtype Context = Context { unContext :: Map.Map Name Value }
  deriving (Eq, Monoid, Ord, Semigroup, Show)

lookup :: Name -> Context -> Maybe Value
lookup n = Map.lookup n . unContext

insert :: Name -> Value -> Context -> Context
insert n v = Context . Map.insert n v . unContext

instance Pretty Context where
  pretty = vsep . map prettyBinding . Map.toList . unContext
    where prettyBinding (name, ty) = pretty name <+> pretty ":" <+> group (pretty ty)
