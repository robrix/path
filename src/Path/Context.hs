{-# LANGUAGE MultiParamTypeClasses #-}
module Path.Context where

import Control.Arrow ((***))
import qualified Data.Map as Map
import Path.Pretty
import Path.Value
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

type Type = Value

newtype Context v = Context { unContext :: Map.Map v (Type v) }
  deriving (Eq, Ord, Show)

empty :: Context v
empty = Context Map.empty

null :: Context v -> Bool
null = Map.null . unContext

lookup :: Ord v => v -> Context v -> Maybe (Type v)
lookup n = Map.lookup n . unContext

insert :: Ord v => v -> Type v -> Context v -> Context v
insert n t = Context . Map.insert n t . unContext

union :: Ord v => Context v -> Context v -> Context v
union (Context c1) (Context c2) = Context (Map.union c1 c2)

filter :: (v -> Type v -> Bool) -> Context v -> Context v
filter f = Context . Map.filterWithKey f . unContext

instance (Ord v, Pretty v) => Pretty (Context v) where
  pretty (Context m) = vsep (map (uncurry prettyBinding) bindings)
    where prettyBinding name ty = group (nest 2 (green (fill maxW name) </> align (pretty ":" <+> group ty)))
          bindings = map (pretty *** pretty) (Map.toList m)
          maxW = maximum (map (length . show . plain . fst) bindings)

instance (Ord v, Pretty v) => PrettyPrec (Context v)

instance Ord v => Semigroup (Context v) where
  Context c1 <> Context c2 = Context (Map.union c1 c2)
