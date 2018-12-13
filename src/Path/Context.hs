{-# LANGUAGE MultiParamTypeClasses #-}
module Path.Context where

import qualified Data.Map as Map
import Path.Eval
import Path.Name
import Path.Pretty
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

type Type = Value

newtype Context = Context { unContext :: Map.Map Name Type }
  deriving (Eq, Ord, Show)

empty :: Context
empty = Context Map.empty

lookup :: Name -> Context -> Maybe Type
lookup n = Map.lookup n . unContext

insert :: Name -> Type -> Context -> Context
insert n t = Context . Map.insert n t . unContext

union :: Context -> Context -> Context
union (Context c1) (Context c2) = Context (Map.union c1 c2)

instance Pretty Context where
  pretty = vsep . map (uncurry prettyBinding) . Map.toList . unContext
    where prettyBinding name ty = pretty name <+> pretty ":" <+> group (pretty ty)

instance PrettyPrec Context

instance Semigroup Context where
  Context c1 <> Context c2 = Context (Map.union c1 c2)
