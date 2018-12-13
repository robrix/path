{-# LANGUAGE MultiParamTypeClasses #-}
module Path.Context where

import Control.Monad ((<=<))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Path.Eval
import Path.Name
import Path.Pretty
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

type Type = Value

newtype Context = Context { unContext :: Map.Map Name (Set.Set Type) }
  deriving (Eq, Ord, Show)

empty :: Context
empty = Context Map.empty

lookup :: Name -> Context -> Maybe Type
lookup n = disambiguate <=< Map.lookup n . unContext

insert :: Name -> Type -> Context -> Context
insert n t = Context . Map.insertWith (<>) n (Set.singleton t) . unContext

union :: Context -> Context -> Context
union (Context c1) (Context c2) = Context (Map.unionWith (<>) c1 c2)

disambiguate :: Set.Set a -> Maybe a
disambiguate tys | [ty] <- Set.toList tys = Just ty
                 | otherwise              = Nothing

instance Pretty Context where
  pretty = vsep . map prettyBindings . Map.toList . unContext
    where prettyBindings (name, tys) = vsep (map (prettyBinding name) (Set.toList tys))
          prettyBinding name ty = pretty name <+> pretty ":" <+> group (pretty ty)

instance PrettyPrec Context

instance Semigroup Context where
  Context c1 <> Context c2 = Context (Map.unionWith (<>) c1 c2)
