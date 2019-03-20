{-# LANGUAGE DeriveTraversable, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, KindSignatures, LambdaCase, MultiParamTypeClasses, StandaloneDeriving, TypeOperators, UndecidableInstances #-}
module Path.Name where

import           Control.Effect
import           Control.Effect.Carrier
import           Control.Effect.Reader hiding (Local)
import           Control.Effect.State
import           Control.Effect.Sum
import           Control.Monad.IO.Class
import           Data.Bifunctor
import           Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Path.Pretty
import           Path.Usage
import           Text.Trifecta.Rendering (Span, Spanned(..))

data Gensym
  = Root String
  | Gensym :/ (String, Int)
  deriving (Eq, Ord, Show)

infixl 6 :/

instance Pretty Gensym where
  pretty = \case
    Root s -> pretty s
    _ :/ (_, i) -> prettyVar i

instance PrettyPrec Gensym

prettyGensym :: Gensym -> Doc
prettyGensym = \case
  Root s -> pretty s
  _ :/ (s, i) -> pretty s <> pretty i

(//) :: Gensym -> String -> Gensym
root // s = root :/ (s, 0)

infixl 6 //


gensym :: (Carrier sig m, Member Naming sig) => String -> m Gensym
gensym s = send (Gensym s pure)

namespace :: (Carrier sig m, Member Naming sig) => String -> m a -> m a
namespace s m = send (Namespace s m pure)

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


runNaming :: Functor m => Gensym -> NamingC m a -> m a
runNaming root = runReader root . evalState 0 . runNamingC

newtype NamingC m a = NamingC { runNamingC :: StateC Int (ReaderC Gensym m) a }
  deriving (Applicative, Functor, Monad, MonadIO)

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

instance PrettyPrec User

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

instance PrettyPrec ModuleName

makeModuleName :: NonEmpty String -> ModuleName
makeModuleName (s:|ss) = foldl (:.) (ModuleName s) ss


type PackageName = String


data Qualified
  = ModuleName :.: User
  deriving (Eq, Ord, Show)

instance Pretty Qualified where
  pretty (m :.: n) = pretty m <> dot <> pretty n


data Name
  = Global Qualified
  | Local Gensym
  deriving (Eq, Ord, Show)

instance Pretty Name where
  pretty = \case
    Global (_ :.: n) -> pretty n
    Local         n  -> pretty '_' <> prettyGensym n

inModule :: ModuleName -> Name -> Bool
inModule m (Global (m' :.: _)) = m == m'
inModule _ _                   = False

prettyQName :: Name -> Doc
prettyQName = \case
  Global n -> pretty n
  Local  n -> pretty '_' <> prettyGensym n


data Meta
  = Name Name
  | Meta Gensym
  deriving (Eq, Ord, Show)

instance Pretty Meta where
  pretty = \case
    Name q -> pretty q
    Meta m -> pretty '?' <> pretty m

qlocal :: Gensym -> Meta
qlocal = Name . Local

localNames :: Set.Set Meta -> Set.Set Gensym
localNames = foldMap (\case { Name (Local v) -> Set.singleton v ; _ -> mempty })

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
showOperator = \case
  Prefix (f:|fs) -> f <> " _ " <> concatMap (\ a -> a <> " _") fs
  Postfix (f:|fs) -> "_ " <> f <> " " <> concatMap (\ a -> "_ " <> a) fs
  Infix (f:|fs) -> "_ " <> f <> " _ " <> concatMap (\ a -> a <> " _") fs
  Closed fs ff -> foldr (\ a rest -> a <> " _ " <> rest) ff fs

instance Pretty Operator where
  pretty = \case
    Prefix (f:|fs) -> pretty f <+> underscore <+> hsep (map (\ a -> pretty a <+> underscore) fs)
    Postfix (f:|fs) -> underscore <+> pretty f <+> hsep (map (\ a -> underscore <+> pretty a) fs)
    Infix (f:|fs) -> underscore <+> pretty f <+> underscore <+> hsep (map (\ a -> pretty a <+> underscore) fs)
    Closed fs ff -> foldr (\ a rest -> pretty a <+> underscore <+> rest) (pretty ff) fs
    where underscore = pretty '_'

instance PrettyPrec Operator


data Incr a = Z | S a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

match :: Eq a => a -> a -> Incr a
match x y | x == y    = Z
          | otherwise = S y

subst :: a -> Incr a -> a
subst a Z     = a
subst _ (S a) = a

incr :: b -> (a -> b) -> Incr a -> b
incr z s = \case { Z -> z ; S a -> s a }


data a ::: b = a ::: b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bifunctor (:::) where
  bimap f g (a ::: b) = f a ::: g b

typedTerm :: a ::: b -> a
typedTerm (a ::: _) = a

typedType :: a ::: b -> b
typedType (_ ::: t) = t

infix 6 :::

instance (Pretty a, Pretty b) => Pretty (a ::: b) where
  pretty (a ::: t) = pretty a <+> colon <+> pretty t

instance (Pretty a, Pretty b) => PrettyPrec (a ::: b)

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
