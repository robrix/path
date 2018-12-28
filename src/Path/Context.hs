module Path.Context where

import Control.Arrow ((***))
import Data.Foldable (toList)
import qualified Data.Set as Set
import Path.Back as Back
import Path.Name
import Path.Pretty
import Path.Value

type Type = Value

data Typed a = a ::: Type QName
  deriving (Eq, Ord, Show)

infix 6 :::

newtype Context = Context { unContext :: Back (QName, Type QName) }
  deriving (Eq, Ord, Show)

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

boundVars :: Context -> Set.Set QName
boundVars = foldMap (Set.singleton . fst) . unContext

instance Pretty Context where
  pretty = tabulate2 (space <> colon <> space) . map (green . pretty *** nest 2 . align . group . pretty) . toList . unContext

instance PrettyPrec Context

instance Semigroup Context where
  Context c1 <> Context c2 = Context (c1 <> c2)

instance Monoid Context where
  mempty = Context Nil
