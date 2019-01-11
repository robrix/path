{-# LANGUAGE LambdaCase, FlexibleInstances, MultiParamTypeClasses #-}
module Path.Name where

import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Path.Pretty
import Path.Usage
import Text.Trifecta.Rendering (Span)

data Name
  = Name String
  | Gensym String Int
  | Op Operator
  deriving (Eq, Ord, Show)

instance Pretty Name where
  pretty = \case
    Name s -> pretty s
    Gensym s i -> pretty s <> prettyVar i
    Op op -> pretty op

instance PrettyPrec Name


data Gensym
  = Root String
  | Gensym :/ (String, Int)
  deriving (Eq, Ord, Show)

infixl 6 :/

instance Pretty Gensym where
  pretty = \case
    Root s -> pretty s
    r :/ (s, i) -> pretty r <> pretty "/" <> pretty s <> prettyVar i

instance PrettyPrec Gensym

(//) :: Gensym -> String -> Gensym
root // s = root :/ (s, 0)

infixl 6 //

prime :: Gensym -> Gensym
prime (root :/ (s, i)) = root :/ (s, succ i)
prime root             = root :/ ("", 0)


data UName
  = UName String
  | UOp Operator
  deriving (Eq, Ord, Show)

instance Pretty UName where
  pretty = \case
    UName s -> pretty s
    UOp op -> pretty op

instance PrettyPrec UName

toName :: UName -> Name
toName (UName s) = Name s
toName (UOp op)  = Op op


newtype Meta = M { unM :: Int }
  deriving (Eq, Ord, Show)

instance Pretty Meta where
  pretty (M i) = pretty "_meta_" <> prettyVar i

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
  | Meta Meta
  | Local Name
  deriving (Eq, Ord, Show)

instance Pretty QName where
  pretty = \case
    _ :.: n -> pretty n
    Meta m -> pretty m
    Local n -> pretty n

inModule :: ModuleName -> QName -> Bool
inModule m (m' :.: _) = m == m'
inModule _ _          = False

isLocal :: QName -> Bool
isLocal (Local _) = True
isLocal _         = False

prettyQName :: QName -> Doc
prettyQName = \case
  m :.: n -> pretty m <> dot <> pretty n
  Meta m -> pretty m
  Local n -> pretty n

localNames :: Set.Set QName -> Set.Set Name
localNames = foldMap (\case { Local v -> Set.singleton v ; _ -> mempty })

metaNames :: Set.Set QName -> Set.Set Meta
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


data Assoc = LAssoc | RAssoc | NonAssoc
  deriving (Eq, Ord, Show)


class Ord v => FreeVariables v a where
  fvs :: a -> Set.Set v

class Ord v => FreeVariables1 v t where
  liftFvs :: (a -> Set.Set v) -> t a -> Set.Set v

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
