{-# LANGUAGE DerivingVia, GeneralizedNewtypeDeriving, TypeOperators #-}
module Path.Namespace where

import Control.Arrow ((***))
import Data.Bifoldable
import Data.Bifunctor
import Data.Coerce
import Data.Functor.Identity
import qualified Data.Map as Map
import Path.Core
import Path.Name
import Path.Pretty

newtype Entry a = Entry { unEntry :: Maybe a ::: a }
  deriving (Eq, Ord, Show)
  deriving (Foldable, Functor) via (Bi (:::) Maybe Identity)

entryType :: Entry a -> a
entryType = typedType . unEntry

entryValue :: Entry a -> Maybe a
entryValue = typedTerm . unEntry

instance Pretty a => Pretty (Entry a) where
  pretty (Entry (Nothing ::: ty)) =         cyan colon <+> pretty ty
  pretty (Entry (Just v  ::: ty)) = align $ cyan colon <+> pretty ty <> hardline <> cyan (pretty "=") <+> pretty v


newtype Namespace = Namespace { unNamespace :: Map.Map Qualified (Entry (Core Qualified)) }
  deriving (Eq, Monoid, Ord, Semigroup, Show)

lookup :: Qualified -> Namespace -> Maybe (Entry (Core Qualified))
lookup q = Map.lookup q . unNamespace

null :: Namespace -> Bool
null = Map.null . unNamespace

union :: Namespace -> Namespace -> Namespace
union = (<>)

filter :: (Qualified -> Entry (Core Qualified) -> Bool) -> Namespace -> Namespace
filter = under . Map.filterWithKey

insert :: Qualified -> Entry (Core Qualified) -> Namespace -> Namespace
insert q = under . Map.insert q

under :: (Map.Map Qualified (Entry (Core Qualified)) -> Map.Map Qualified (Entry (Core Qualified))) -> Namespace -> Namespace
under = coerce

instance Pretty Namespace where
  pretty = tabulate2 space . map (green . pretty *** align . group . pretty) . Map.toList . unNamespace


-- | A functor composing two functors on the inside of a bifunctor. Can be used with @-XDerivingVia@ to derive 'Foldable', 'Functor', and 'Traversable' instances given 'Bifoldable', 'Bifunctor', and 'Bitraversable' instances for @p@ respectively.
newtype Bi p f g a = Bi { unBi :: p (f a) (g a) }

instance (Bifoldable p, Foldable f, Foldable g) => Foldable (Bi p f g) where
  foldMap f = bifoldMap (foldMap f) (foldMap f) . unBi

instance (Bifunctor p, Functor f, Functor g) => Functor (Bi p f g) where
  fmap f = Bi . bimap (fmap f) (fmap f) . unBi
