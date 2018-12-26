{-# LANGUAGE LambdaCase #-}
module Path.Name where

import Data.List.NonEmpty (NonEmpty(..))
import Path.Pretty
import Text.PrettyPrint.ANSI.Leijen

data Name
  = Name String
  | Gensym Int
  | Op Operator
  deriving (Eq, Ord, Show)

instance Pretty Name where
  pretty = \case
    Name s -> pretty s
    Gensym i -> pretty ('_' : alphabet !! q : show r)
      where (q, r) = i `divMod` 26
            alphabet = ['a'..'z']
    Op op -> pretty op

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


data Twin = Only | TwinL | TwinR
  deriving (Eq, Ord, Show)

data Var v = V v Twin | M v
  deriving (Eq, Ord, Show)


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


data Assoc = L | R | Non
  deriving (Eq, Ord, Show)
