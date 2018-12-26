module Path.Context where

import Control.Arrow ((***))
import Data.Foldable (toList)
import Path.Back as Back
import Path.Name
import Path.Pretty
import Path.Value
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

type Type = Value

newtype Context = Context { unContext :: Back (QName, Type QName) }
  deriving (Eq, Ord, Show)

empty :: Context
empty = Context Nil

null :: Context -> Bool
null = Prelude.null . unContext

lookup :: QName -> Context -> Maybe (Type QName)
lookup n = Back.lookup n . unContext

insert :: QName -> Type QName -> Context -> Context
insert n t = Context . (:> (n, t)) . unContext

union :: Context -> Context -> Context
union (Context c1) (Context c2) = Context (c1 <> c2)

filter :: (QName -> Type QName -> Bool) -> Context -> Context
filter f = Context . Back.filter (uncurry f) . unContext

instance Pretty Context where
  pretty = tabulate2 (space <> colon <> space) . map (green . pretty *** nest 2 . align . group . pretty) . toList . unContext

instance PrettyPrec Context

instance Semigroup Context where
  Context c1 <> Context c2 = Context (c1 <> c2)
