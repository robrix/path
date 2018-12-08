module Path.Context where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Path.Eval
import Path.Name
import Text.PrettyPrint.ANSI.Leijen

type Type = Value

newtype Context = Context { unContext :: Map.Map Name (Set.Set Type) }
  deriving (Eq, Ord, Show)

empty :: Context
empty = Context Map.empty

lookup :: Name -> Context -> Maybe (Set.Set Type)
lookup n = Map.lookup n . unContext

insert :: Name -> Type -> Context -> Context
insert n v = Context . Map.insertWith (<>) n (Set.singleton v) . unContext

union :: Context -> Context -> Context
union (Context c1) (Context c2) = Context (Map.unionWith (<>) c1 c2)

disambiguate :: Set.Set a -> Maybe a
disambiguate tys | [ty] <- Set.toList tys = Just ty
                 | otherwise              = Nothing

instance Pretty Context where
  pretty = vsep . map prettyBindings . Map.toList . unContext
    where prettyBindings (name, tys) = vsep (map (prettyBinding name) (Set.toList tys))
          prettyBinding name ty = pretty name <+> pretty ":" <+> group (pretty ty)
