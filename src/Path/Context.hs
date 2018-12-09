{-# LANGUAGE MultiParamTypeClasses #-}
module Path.Context where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Tuple (swap)
import Path.Eval
import Path.Name
import Path.Pretty
import Path.Semiring
import Path.Usage
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

type Type = Value

newtype Context = Context { unContext :: Map.Map Name (Map.Map Type Usage) }
  deriving (Eq, Ord, Show)

empty :: Context
empty = Context Map.empty

lookup :: Name -> Context -> Maybe (Set.Set (Usage, Type))
lookup n = fmap toSet . Map.lookup n . unContext
  where toSet = Set.fromList . map swap . Map.assocs

insert :: Name -> (Usage, Type) -> Context -> Context
insert n (u, t) = Context . Map.insertWith (<>) n (Map.singleton t u) . unContext

union :: Context -> Context -> Context
union (Context c1) (Context c2) = Context (Map.unionWith (<>) c1 c2)

disambiguate :: Set.Set a -> Maybe a
disambiguate tys | [ty] <- Set.toList tys = Just ty
                 | otherwise              = Nothing

instance Pretty Context where
  pretty = vsep . map prettyBindings . Map.toList . unContext
    where prettyBindings (name, tys) = vsep (map (prettyBinding name) (Map.toList tys))
          prettyBinding name (ty, u) = pretty name <+> pretty ":" <> prettyUsage u <+> group (pretty ty)
          prettyUsage Zero = pretty "⁰"
          prettyUsage One  = pretty "¹"
          prettyUsage More = pretty "ⁿ"

instance PrettyPrec Context

instance Semigroup Context where
  Context c1 <> Context c2 = Context (Map.unionWith (Map.unionWith (<>)) c1 c2)

instance LeftModule Usage Context where
  u ><< Context c = Context (fmap (u ><) <$> c)


type Resources = Map.Map Name Usage
