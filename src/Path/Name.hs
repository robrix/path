{-# LANGUAGE DeriveTraversable, LambdaCase #-}
module Path.Name where

import           Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Set as Set
import           Path.Pretty

type User = String


data ModuleName
  = ModuleName String
  | ModuleName :. String
  deriving (Eq, Ord, Show)

infixl 5 :.

instance Pretty ModuleName where
  pretty = \case
    ModuleName s -> pretty s
    ss :. s      -> pretty ss <> dot <> pretty s

makeModuleName :: NonEmpty String -> ModuleName
makeModuleName (s:|ss) = foldl (:.) (ModuleName s) ss


type PackageName = String


data Qualified
  = ModuleName :.: User
  deriving (Eq, Ord, Show)

infixl 5 :.:

instance Pretty Qualified where
  pretty (m :.: n) = pretty m <> dot <> pretty n


fvs :: (Foldable t, Ord a) => t a -> Set.Set a
fvs = foldMap Set.singleton


data Named a b = Named (Ignored a) b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

named :: a -> b -> Named a b
named = Named . Ignored

namedName :: Named a b -> a
namedName (Named (Ignored a) _) = a

namedValue :: Named a b -> b
namedValue (Named _ b) = b


newtype Ignored a = Ignored a
  deriving (Foldable, Functor, Show, Traversable)

instance Eq  (Ignored a) where _ == _ = True
instance Ord (Ignored a) where compare _ _ = EQ

unIgnored :: Ignored a -> a
unIgnored (Ignored a) = a
