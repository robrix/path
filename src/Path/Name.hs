{-# LANGUAGE DeriveTraversable, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, KindSignatures, LambdaCase, MultiParamTypeClasses, QuantifiedConstraints, StandaloneDeriving, TypeOperators, UndecidableInstances #-}
module Path.Name where

import           Control.Applicative (Alternative (..))
import           Control.Effect
import           Control.Effect.Carrier
import           Control.Effect.Reader hiding (Local)
import           Control.Effect.State
import           Control.Effect.Sum
import           Control.Monad ((>=>))
import           Control.Monad.Fail
import           Control.Monad.IO.Class
import           Data.Bifunctor
import           Data.Function (on)
import           Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Path.Pretty
import           Path.Stack
import           Path.Usage
import           Prelude hiding (fail)
import           Text.Trifecta.Rendering (Span, Spanned(..))

data Gensym
  = Root
  | Gensym :/ (String, Int)
  deriving (Eq, Ord, Show)

infixl 6 :/

instance Pretty Gensym where
  pretty = \case
    Root -> pretty "◊"
    _ :/ (_, i) -> prettyVar i

prettyGensym :: Gensym -> Doc
prettyGensym = \case
  Root -> pretty "◊"
  _ :/ ("", i) -> prettyVar i
  _ :/ (s, i) -> pretty s <> pretty i

(//) :: Gensym -> String -> Gensym
root // s = root :/ (s, 0)

infixl 6 //


gensym :: (Carrier sig m, Member Naming sig) => String -> m Gensym
gensym s = send (Gensym s pure)

namespace :: (Carrier sig m, Member Naming sig) => String -> m a -> m a
namespace s m = send (Namespace s m pure)


un :: (Carrier sig m, Member Naming sig) => (Gensym -> t -> Either b (a, t)) -> t -> m (Stack a, b)
un from = go Nil
  where go names value = do
          name <- gensym ""
          case from name value of
            Right (name, body) -> go (names :> name) body
            Left body          -> pure (names, body)

orTerm :: (n -> t -> Maybe (a, t)) -> (n -> t -> Either t (a, t))
orTerm f a t = maybe (Left t) Right (f a t)

data Naming m k
  = Gensym String (Gensym -> k)
  | forall a . Namespace String (m a) (a -> k)

deriving instance Functor (Naming m)

instance HFunctor Naming where
  hmap _ (Gensym    s   k) = Gensym s k
  hmap f (Namespace s m k) = Namespace s (f m) k

instance Effect Naming where
  handle state handler (Gensym    s   k) = Gensym s (handler . (<$ state) . k)
  handle state handler (Namespace s m k) = Namespace s (handler (m <$ state)) (handler . fmap k)


runNaming :: Functor m => NamingC m a -> m a
runNaming = runReader Root . evalState 0 . runNamingC

newtype NamingC m a = NamingC { runNamingC :: StateC Int (ReaderC Gensym m) a }
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)

instance (Carrier sig m, Effect sig) => Carrier (Naming :+: sig) (NamingC m) where
  eff (L (Gensym    s   k)) = NamingC (StateC (\ i -> (:/ (s, i)) <$> ask >>= runState (succ i) . runNamingC . k))
  eff (L (Namespace s m k)) = NamingC (StateC (\ i -> local (// s) (evalState 0 (runNamingC m)) >>= runState i . runNamingC . k))
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

inModule :: ModuleName -> Name Gensym -> Bool
inModule m (Global (m' :.: _)) = m == m'
inModule _ _                   = False

prettyQName :: Name Gensym -> Doc
prettyQName = \case
  Global n -> pretty n
  Local  n -> pretty '_' <> prettyGensym n


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


data Incr a = Z | S a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

match :: Eq a => a -> a -> Incr a
match x y | x == y    = Z
          | otherwise = S y

subst :: a -> Incr a -> a
subst a = incr a id

incr :: b -> (a -> b) -> Incr a -> b
incr z s = \case { Z -> z ; S a -> s a }

-- | Bind occurrences of a variable in a term, producing a term in which the variable is bound.
bind :: (Applicative f, Eq a) => a -> f a -> f (Incr (f a))
bind name = fmap (fmap pure . match name)

-- | Substitute a term for the free variable in a given term, producing a closed term.
instantiate :: Monad f => f a -> f (Incr (f a)) -> f a
instantiate t b = b >>= subst t


newtype Scope f a = Scope { unScope :: f (Incr (f a)) }
  deriving (Foldable, Functor, Traversable)

instance (Monad f, Eq  a, forall a . Eq  a => Eq  (f a)) => Eq  (Scope f a) where
  (==) = (==) `on` flattenScope

instance (Monad f, Ord a, forall a . Eq  a => Eq  (f a)
                        , forall a . Ord a => Ord (f a)) => Ord (Scope f a) where
  compare = compare `on` flattenScope

deriving instance (Show a, forall a . Show a => Show (f a)) => Show (Scope f a)

flattenScope :: Monad f => Scope f a -> f (Incr a)
flattenScope = unScope >=> sequenceA


data a ::: b = a ::: b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bifunctor (:::) where
  bimap f g (a ::: b) = f a ::: g b

typedTerm :: a ::: b -> a
typedTerm (a ::: _) = a

typedType :: a ::: b -> b
typedType (_ ::: t) = t

infix 7 :::

instance (Pretty a, Pretty b) => Pretty (a ::: b) where
  pretty (a ::: t) = pretty a <+> cyan colon <+> pretty t

instance (FreeVariables v a, FreeVariables v b) => FreeVariables v (a ::: b) where
  fvs (a ::: b) = fvs a <> fvs b


data Assoc = LAssoc | RAssoc | NonAssoc
  deriving (Eq, Ord, Show)


class Ord v => FreeVariables v a where
  fvs :: a -> Set.Set v

instance Ord v => FreeVariables v () where
  fvs _ = Set.empty

instance (FreeVariables v a, FreeVariables v b) => FreeVariables v (a, b) where
  fvs (a, b) = fvs a <> fvs b

instance (FreeVariables v key, FreeVariables v value) => FreeVariables v (Map.Map key value) where
  fvs = fvs . Map.toList

instance FreeVariables v a => FreeVariables v [a] where
  fvs = foldMap fvs

instance Ord v => FreeVariables v v where
  fvs = Set.singleton

instance Ord v => FreeVariables v (Set.Set v) where
  fvs = id

instance Ord v => FreeVariables v Usage where
  fvs _ = Set.empty

instance Ord v => FreeVariables v Span where
  fvs _ = mempty

instance FreeVariables v a => FreeVariables v (Spanned a) where
  fvs (a :~ _) = fvs a
