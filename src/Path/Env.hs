{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Path.Env where

import qualified Data.Map as Map
import Path.Pretty
import Path.Value
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

newtype Env v = Env { unEnv :: Map.Map v (Value v) }
  deriving (Eq, Monoid, Ord, Semigroup, Show)

empty :: Env v
empty = Env Map.empty

null :: Env v -> Bool
null = Map.null . unEnv

lookup :: Ord v => v -> Env v -> Maybe (Value v)
lookup n = Map.lookup n . unEnv

insert :: Ord v => v -> Value v -> Env v -> Env v
insert n v = Env . Map.insert n v . unEnv

union :: Ord v => Env v -> Env v -> Env v
union (Env e1) (Env e2) = Env (Map.union e1 e2)

filter :: (v -> Value v -> Bool) -> Env v -> Env v
filter f = Env . Map.filterWithKey f . unEnv

instance (Ord v, Pretty v) => Pretty (Env v) where
  pretty = vsep . map (uncurry prettyBinding) . Map.toList . unEnv
    where prettyBinding name ty = green (pretty name) <+> pretty "=" <+> group (pretty ty)

instance (Ord v, Pretty v) => PrettyPrec (Env v)
