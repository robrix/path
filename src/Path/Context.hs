module Path.Context where

import Control.Arrow ((&&&))
import Data.Foldable (toList)
import qualified Data.Set as Set
import Path.Back as Back
import Path.Name
import Path.Pretty
import Path.Value

newtype Context = Context { unContext :: Back (Typed Name) }
  deriving (Eq, Ord, Show)

null :: Context -> Bool
null = Prelude.null . unContext

lookup :: Name -> Context -> Maybe Type
lookup n = fmap typedType . Back.find ((== n) . typedTerm) . unContext

insert :: Typed Name -> Context -> Context
insert t = Context . (:> t) . unContext

union :: Context -> Context -> Context
union (Context c1) (Context c2) = Context (c1 <> c2)

filter :: (Typed Name -> Bool) -> Context -> Context
filter f = Context . Back.filter f . unContext

boundVars :: Context -> Set.Set Name
boundVars = foldMap (Set.singleton . typedTerm) . unContext

nub :: Context -> Context
nub = Context . go mempty . unContext
  where go _ Nil = Nil
        go v (init :> last)
          | typedTerm last `Set.member` v = go v init
          | otherwise                   = go (Set.insert (typedTerm last) v) init :> last

instance Pretty Context where
  pretty = tabulate2 (space <> colon <> space) . map (green . pretty . typedTerm &&& nest 2 . align . group . pretty . typedType) . toList . unContext

instance PrettyPrec Context

instance Semigroup Context where
  Context c1 <> Context c2 = Context (c1 <> c2)

instance Monoid Context where
  mempty = Context Nil
