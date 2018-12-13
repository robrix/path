{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Path.Env where

import qualified Data.Map as Map
import Path.Pretty
import Path.Value
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

newtype Env = Env { unEnv :: Map.Map String Value }
  deriving (Eq, Monoid, Ord, Semigroup, Show)

empty :: Env
empty = Env Map.empty

lookup :: String -> Env -> Maybe Value
lookup n = Map.lookup n . unEnv

insert :: String -> Value -> Env -> Env
insert n v = Env . Map.insert n v . unEnv

union :: Env -> Env -> Env
union (Env e1) (Env e2) = Env (Map.union e1 e2)

instance Pretty Env where
  pretty = vsep . map (uncurry prettyBinding) . Map.toList . unEnv
    where prettyBinding name ty = pretty name <+> pretty "=" <+> group (pretty ty)

instance PrettyPrec Env
