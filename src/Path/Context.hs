module Path.Context where

import Control.Arrow ((***))
import Data.Foldable (toList)
import Path.Back as Back
import Path.Pretty
import Path.Value
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

type Type = Value

newtype Context v = Context { unContext :: Back (v, Type) }
  deriving (Eq, Ord, Show)

empty :: Context v
empty = Context Nil

null :: Context v -> Bool
null = Prelude.null . unContext

lookup :: Eq v => v -> Context v -> Maybe Type
lookup n = Back.lookup n . unContext

insert :: v -> Type -> Context v -> Context v
insert n t = Context . (:> (n, t)) . unContext

union :: Context v -> Context v -> Context v
union (Context c1) (Context c2) = Context (c1 <> c2)

filter :: (v -> Type -> Bool) -> Context v -> Context v
filter f = Context . Back.filter (uncurry f) . unContext

instance (Ord v, Pretty v) => Pretty (Context v) where
  pretty = tabulate2 (space <> colon <> space) . map (green . pretty *** nest 2 . align . group . pretty) . toList . unContext

instance (Ord v, Pretty v) => PrettyPrec (Context v)

instance Semigroup (Context v) where
  Context c1 <> Context c2 = Context (c1 <> c2)
