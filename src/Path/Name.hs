{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, KindSignatures, LambdaCase, MultiParamTypeClasses, TypeOperators, UndecidableInstances #-}
module Path.Name where

import           Control.Effect
import           Control.Effect.Carrier
import           Control.Effect.Fresh
import           Control.Effect.Reader hiding (Local)
import           Control.Effect.Sum
import           Data.Bifunctor
import           Data.Coerce
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

(//) :: Gensym -> String -> Gensym
root // s = root :/ (s, 0)

infixl 6 //

gensym :: (Applicative m, Carrier sig m, Member Fresh sig, Member (Reader Gensym) sig) => String -> m Gensym
gensym s = (:/) <$> ask <*> ((,) s <$> fresh)


data Naming (m :: * -> *) k
  = Gensym String (Gensym -> k)
  deriving (Functor)

instance HFunctor Naming where
  hmap _ = coerce

instance Effect Naming where
  handle state handler = coerce . fmap (handler . (<$ state))


runNaming :: Functor m => Gensym -> NamingC m a -> m a
runNaming root = runReader root . runFresh . runNamingC

newtype NamingC m a = NamingC { runNamingC :: FreshC (ReaderC Gensym m) a }
  deriving (Applicative, Functor, Monad)

instance (Carrier sig m, Effect sig) => Carrier (Naming :+: sig) (NamingC m) where
  eff (L (Gensym s k)) = NamingC ((:/) <$> ask <*> ((,) s <$> fresh)) >>= k
  eff (R other)        = NamingC (eff (R (R (handleCoercible other))))


data User
  = User String
  | Op Operator
  deriving (Eq, Ord, Show)

instance Pretty User where
  pretty = \case
    User s -> pretty s
    Op op -> pretty op

instance PrettyPrec User


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


data Qual
  = ModuleName :.: User
  | Local Gensym
  deriving (Eq, Ord, Show)

instance Pretty Qual where
  pretty = \case
    _ :.: n -> pretty n
    Local n -> pretty n

inModule :: ModuleName -> Qual -> Bool
inModule m (m' :.: _) = m == m'
inModule _ _          = False

prettyQName :: Qual -> Doc
prettyQName = \case
  m :.: n -> pretty m <> dot <> pretty n
  Local n -> pretty n


data Meta
  = Qual Qual
  | Meta Gensym
  deriving (Eq, Ord, Show)

instance Pretty Meta where
  pretty = \case
    Qual q -> pretty q
    Meta m -> pretty '?' <> pretty m

qlocal :: Gensym -> Meta
qlocal = Qual . Local

localNames :: Set.Set Meta -> Set.Set Gensym
localNames = foldMap (\case { Qual (Local v) -> Set.singleton v ; _ -> mempty })

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
