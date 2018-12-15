module Path.Name where

import Data.List.NonEmpty (NonEmpty(..))
import Path.Pretty
import Text.PrettyPrint.ANSI.Leijen

data Name
  = Name String
  | Gensym Int
  deriving (Eq, Ord, Show)

instance Pretty Name where
  pretty (Name s) = pretty s
  pretty (Gensym i) = pretty ('_' : alphabet !! q : show r)
    where (q, r) = i `divMod` 26
          alphabet = ['a'..'z']

instance PrettyPrec Name


data ModuleName
  = ModuleName String
  | ModuleName :. String
  deriving (Eq, Ord, Show)

infixl 5 :.

instance Pretty ModuleName where
  pretty (ModuleName s) = pretty s
  pretty (ss :. s) = pretty ss <> dot <> pretty s

instance PrettyPrec ModuleName

makeModuleName :: NonEmpty String -> ModuleName
makeModuleName (s:|ss) = foldl (:.) (ModuleName s) ss


type PackageName = String


data QName
  = ModuleName :.: Name
  | Local Name
  deriving (Eq, Ord, Show)

instance Pretty QName where
  pretty (_ :.: n) = pretty n
  pretty (Local n) = pretty n

inModule :: ModuleName -> QName -> Bool
inModule m (m' :.: _) = m == m'
inModule _ _          = False

isLocal :: QName -> Bool
isLocal (Local _) = True
isLocal _         = False
