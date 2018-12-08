{-# LANGUAGE MultiParamTypeClasses #-}
module Path.Context where

import Data.Bifunctor (first)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Path.Eval
import Path.Name
import Path.Semiring
import Path.Usage
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

type Type = Value

newtype Context = Context { unContext :: Map.Map Name (Set.Set (Usage, Type)) }
  deriving (Eq, Ord, Show)

empty :: Context
empty = Context Map.empty

lookup :: Name -> Context -> Maybe (Set.Set (Usage, Type))
lookup n = Map.lookup n . unContext

insert :: Name -> (Usage, Type) -> Context -> Context
insert n v = Context . Map.insertWith (<>) n (Set.singleton v) . unContext

union :: Context -> Context -> Context
union (Context c1) (Context c2) = Context (Map.unionWith (<>) c1 c2)

disambiguate :: Set.Set a -> Maybe a
disambiguate tys | [ty] <- Set.toList tys = Just ty
                 | otherwise              = Nothing

instance Pretty Context where
  pretty = vsep . map prettyBindings . Map.toList . unContext
    where prettyBindings (name, tys) = vsep (map (prettyBinding name) (Set.toList tys))
          prettyBinding name (u, ty) = pretty name <+> pretty ":" <> prettyUsage u <+> group (pretty ty)
          prettyUsage Zero = pretty "⁰"
          prettyUsage One  = pretty "¹"
          prettyUsage More = pretty "ⁿ"

instance LeftModule Usage Context where
  u ><< Context c = Context (Set.map (first (u ><)) <$> c)
