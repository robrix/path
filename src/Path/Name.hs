{-# LANGUAGE DeriveTraversable, FlexibleContexts, FlexibleInstances, LambdaCase, MultiParamTypeClasses #-}
module Path.Name where

import           Control.Effect
import           Control.Effect.Fresh
import           Control.Effect.Reader hiding (Local)
import           Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Path.Pretty
import           Path.Usage
import           Text.Trifecta.Rendering (Span)

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

prime :: Gensym -> Gensym
prime (root :/ (s, i)) = root :/ (s, succ i)
prime root             = root :/ ("", 0)

gensym :: (Applicative m, Carrier sig m, Member Fresh sig, Member (Reader Gensym) sig) => String -> m Gensym
gensym s = (:/) <$> ask <*> ((,) s <$> fresh)


data UName
  = UName String
  | UOp Operator
  deriving (Eq, Ord, Show)

instance Pretty UName where
  pretty = \case
    UName s -> pretty s
    UOp op -> pretty op

instance PrettyPrec UName


newtype Meta = Meta { unMeta :: Gensym }
  deriving (Eq, Ord, Show)

instance Pretty Meta where
  pretty (Meta i) = pretty i

instance PrettyPrec Meta


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


data QName
  = ModuleName :.: UName
  | Local Gensym
  deriving (Eq, Ord, Show)

instance Pretty QName where
  pretty = \case
    _ :.: n -> pretty n
    Local n -> pretty n

inModule :: ModuleName -> QName -> Bool
inModule m (m' :.: _) = m == m'
inModule _ _          = False

prettyQName :: QName -> Doc
prettyQName = \case
  m :.: n -> pretty m <> dot <> pretty n
  Local n -> pretty n

localNames :: Set.Set MName -> Set.Set Gensym
localNames = foldMap (\case { Q (Local v) -> Set.singleton v ; _ -> mempty })


data MName
  = Q QName
  | M Meta
  deriving (Eq, Ord, Show)

instance Pretty MName where
  pretty = \case
    Q q -> pretty q
    M m -> pretty m

qlocal :: Gensym -> MName
qlocal = Q . Local

metaNames :: Set.Set MName -> Set.Set Meta
metaNames = foldMap (\case { M m -> Set.singleton m ; _ -> mempty })


data Head a
  = Free a
  | Bound Int
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Ord a => FreeVariables a (Head a) where
  fvs (Free q) = Set.singleton q
  fvs _        = mempty

instance Pretty a => Pretty (Head a) where
  pretty (Free q)  = pretty q
  pretty (Bound i) = prettyVar i

instance Pretty a => PrettyPrec (Head a)


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
