{-# LANGUAGE MultiParamTypeClasses #-}
module Path.Context where

import qualified Data.Map as Map
import Path.Eval
import Path.Pretty
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

type Type = Value

newtype Context v = Context { unContext :: Map.Map v Type }
  deriving (Eq, Ord, Show)

empty :: Context v
empty = Context Map.empty

lookup :: Ord v => v -> Context v -> Maybe Type
lookup n = Map.lookup n . unContext

insert :: Ord v => v -> Type -> Context v -> Context v
insert n t = Context . Map.insert n t . unContext

union :: Ord v => Context v -> Context v -> Context v
union (Context c1) (Context c2) = Context (Map.union c1 c2)

instance Pretty v => Pretty (Context v) where
  pretty = vsep . map (uncurry prettyBinding) . Map.toList . unContext
    where prettyBinding name ty = pretty name <+> pretty ":" <+> group (pretty ty)

instance Pretty v => PrettyPrec (Context v)

instance Ord v => Semigroup (Context v) where
  Context c1 <> Context c2 = Context (Map.union c1 c2)
