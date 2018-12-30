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
  | Gensym Int
  | Meta Int
  | Op Operator
  deriving (Eq, Ord, Show)

newtype MetaVar = M Int
  deriving (Eq, Ord, Show)

instance Pretty Name where
  pretty = \case
    Name s -> pretty s
    Gensym i -> pretty '_' <> prettyI i
    Meta i -> pretty "__" <> prettyI i
    Op op -> pretty op

prettyI :: Int -> Doc
prettyI i = pretty (alphabet !! q : show r)
    where (q, r) = i `divMod` 26
          alphabet = ['a'..'z']

instance PrettyPrec Name


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
  = ModuleName :.: Name
  | Local Name
  deriving (Eq, Ord, Show)

instance Pretty QName where
  pretty = \case
    _ :.: n -> pretty n
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
  Local n -> pretty n


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
