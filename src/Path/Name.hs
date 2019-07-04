{-# LANGUAGE DeriveTraversable, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, KindSignatures, LambdaCase, MultiParamTypeClasses, StandaloneDeriving, TypeApplications, TypeOperators, UndecidableInstances #-}
module Path.Name where

import           Control.Applicative (Alternative (..))
import           Control.Effect
import           Control.Effect.Carrier
import           Control.Effect.Reader hiding (Local)
import           Control.Effect.State
import           Control.Effect.Sum
import           Control.Monad.Fail
import           Control.Monad.IO.Class
import           Data.Bifoldable
import           Data.Bifunctor
import           Data.Bitraversable
import           Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Set as Set
import           Path.Pretty
import           Path.Stack
import           Prelude hiding (fail)

data Gensym = Gensym (Stack String) Int
  deriving (Eq, Ord, Show)

instance Pretty Gensym where
  pretty (Gensym _ i) = prettyVar i

prime :: Gensym -> Gensym
prime (Gensym s i) = Gensym s (succ i)


fresh :: (Carrier sig m, Member Naming sig) => m Gensym
fresh = send (Fresh pure)

namespace :: (Carrier sig m, Member Naming sig) => String -> m a -> m a
namespace s m = send (Namespace s m pure)


un :: Monad m => (t -> Maybe (m (a, t))) -> t -> m (Stack a, t)
un from = unH (\ t -> maybe (Left t) Right (from t))

unH :: Monad m => (t -> Either b (m (a, t))) -> t -> m (Stack a, b)
unH from = go Nil
  where go names value = case from value of
          Right a -> do
            (name, body) <- a
            go (names :> name) body
          Left  b -> pure (names, b)

data Naming m k
  = Fresh (Gensym -> k)
  | forall a . Namespace String (m a) (a -> k)

deriving instance Functor (Naming m)

instance HFunctor Naming where
  hmap _ (Fresh         k) = Fresh             k
  hmap f (Namespace s m k) = Namespace s (f m) k

instance Effect Naming where
  handle state handler (Fresh         k) = Fresh                              (handler . (<$ state) . k)
  handle state handler (Namespace s m k) = Namespace s (handler (m <$ state)) (handler . fmap k)


runNaming :: Functor m => NamingC m a -> m a
runNaming = runReader Nil . evalState 0 . runNamingC

newtype NamingC m a = NamingC { runNamingC :: StateC Int (ReaderC (Stack String) m) a }
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)

instance (Carrier sig m, Effect sig) => Carrier (Naming :+: sig) (NamingC m) where
  eff (L (Fresh         k)) = NamingC (asks Gensym <*> get <* modify (succ @Int) >>= runNamingC . k)
  eff (L (Namespace s m k)) = NamingC (StateC (\ i -> local (:> s) (evalState 0 (runNamingC m)) >>= runState i . runNamingC . k))
  eff (R other)             = NamingC (eff (R (R (handleCoercible other))))


data User
  = Id String
  | Op Operator
  deriving (Eq, Ord, Show)

instance Pretty User where
  pretty = \case
    Id s  -> pretty s
    Op op -> parens (pretty op)

showUser :: User -> String
showUser (Id s) = s
showUser (Op o) = showOperator o


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
    Global (_ :.: n) -> pretty n
    Local         n  -> pretty n

name :: (a -> b) -> (Qualified -> b) -> Name a -> b
name local _      (Local  n) = local n
name _     global (Global n) = global n


localNames :: Ord a => Set.Set (Name a) -> Set.Set a
localNames = foldMap (name Set.singleton (const Set.empty))


close :: (Alternative m, Traversable t) => t (Name a) -> m (t Qualified)
close = traverse (name (const empty) pure)

closeFail :: (MonadFail m, Show a, Traversable t) => t (Name a) -> m (t Qualified)
closeFail = traverse (name (fail . ("free variable: " ++) . show) pure)


data Meta
  = Name Gensym
  | Meta Gensym
  deriving (Eq, Ord, Show)

instance Pretty Meta where
  pretty = \case
    Name q -> pretty q
    Meta m -> dullblack (bold (pretty '?' <> pretty m))

metaNames :: Set.Set Meta -> Set.Set Gensym
metaNames = foldMap (\case { Meta m -> Set.singleton m ; _ -> mempty })


data Operator
  = Prefix (NonEmpty String)
  | Postfix (NonEmpty String)
  | Infix (NonEmpty String)
  | Closed (NonEmpty String) String
  deriving (Eq, Ord, Show)

betweenOp :: String -> String -> Operator
betweenOp a b = Closed (a :| []) b

showOperator :: Operator -> String
showOperator = renderOperator " " id

renderOperator :: Monoid m => m -> (String -> m) -> Operator -> m
renderOperator space pretty = \case
  Prefix (f:|fs) -> hsep (map (\ a -> pretty a <+> underscore) (f:fs))
  Postfix (f:|fs) -> hsep (map (\ a -> underscore <+> pretty a) (f:fs))
  Infix (f:|fs) -> underscore <+> hsep (map (\ a -> pretty a <+> underscore) (f:fs))
  Closed fs ff -> foldr (\ a rest -> pretty a <+> underscore <+> rest) (pretty ff) fs
  where hsep []     = mempty
        hsep [a]    = a
        hsep (a:as) = a <+> hsep as
        s <+> t = s <> space <> t
        underscore = pretty "_"

instance Pretty Operator where
  pretty = renderOperator space pretty


data a ::: b = a ::: b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bifoldable (:::) where
  bifoldMap f g (a ::: b) = f a <> g b

instance Bifunctor (:::) where
  bimap f g (a ::: b) = f a ::: g b

instance Bitraversable (:::) where
  bitraverse f g (a ::: b) = (:::) <$> f a <*> g b

typedTerm :: a ::: b -> a
typedTerm (a ::: _) = a

typedType :: a ::: b -> b
typedType (_ ::: t) = t

infix 7 :::

instance (Pretty a, Pretty b) => Pretty (a ::: b) where
  pretty (a ::: t) = pretty a <+> cyan colon <+> pretty t


-- | A functor composing two functors on the inside of a bifunctor. Can be used with @-XDerivingVia@ to derive 'Foldable', 'Functor', and 'Traversable' instances given 'Bifoldable', 'Bifunctor', and 'Bitraversable' instances for @p@ respectively.
newtype Comp2 p f g a = Comp2 { unComp2 :: p (f a) (g a) }

instance (Bifoldable p, Foldable f, Foldable g) => Foldable (Comp2 p f g) where
  foldMap f = bifoldMap (foldMap f) (foldMap f) . unComp2

instance (Bifunctor p, Functor f, Functor g) => Functor (Comp2 p f g) where
  fmap f = Comp2 . bimap (fmap f) (fmap f) . unComp2


data Assoc = LAssoc | RAssoc | NonAssoc
  deriving (Eq, Ord, Show)


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
