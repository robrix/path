{-# LANGUAGE DeriveTraversable, FlexibleContexts, GeneralizedNewtypeDeriving, LambdaCase, TypeApplications #-}
module Path.Name where

import           Control.Applicative (Alternative (..))
import           Control.Effect.Reader hiding (Local)
import           Control.Monad.Fail
import           Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Set as Set
import           Data.Validation
import           Path.Pretty
import           Path.Stack
import           Prelude hiding (fail)

newtype N = N { unN :: Int }
  deriving (Enum, Eq, Ord, Show)

instance Pretty N where
  pretty (N i) = prettyVar i

bindN :: (Carrier sig m, Member (Reader N) sig) => (N -> m a) -> m a
bindN f = do
  n <- ask
  local @N succ (f n)


un :: Monad m => (t -> Maybe (m (a, t))) -> t -> m (Stack a, t)
un from = unEither (\ t -> maybe (Left t) Right (from t))

unEither :: Monad m => (t -> Either b (m (a, t))) -> t -> m (Stack a, b)
unEither from = go Nil
  where go names value = case from value of
          Right a -> do
            (name, body) <- a
            go (names :> name) body
          Left  b -> pure (names, b)


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


data Name a
  = Global Qualified
  | Local a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Pretty a => Pretty (Name a) where
  pretty = \case
    Global n -> pretty n
    Local  n -> pretty n

name :: (a -> b) -> (Qualified -> b) -> Name a -> b
name local _      (Local  n) = local n
name _     global (Global n) = global n

global :: Applicative m => Qualified -> m (Name a)
global = pure . Global


close :: (Alternative m, Traversable t) => t (Name a) -> m (t Qualified)
close = traverse (name (const empty) pure)

closeFail :: (MonadFail m, Show a, Traversable t) => t (Name a) -> m (t Qualified)
closeFail = traverse (name (fail . ("free variable: " ++) . show) pure)


weaken :: Functor f => f Qualified -> f (Name a)
weaken = fmap Global

strengthen :: Traversable t => t (Name n) -> Either (NonEmpty n) (t Qualified)
strengthen = toEither . traverse (name (Failure . pure) Success)


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
