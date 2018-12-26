{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Path.Env where

import Control.Arrow ((***))
import qualified Data.Map as Map
import Path.Pretty
import Path.Value
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

newtype Env v = Env { unEnv :: Map.Map v Value }
  deriving (Eq, Monoid, Ord, Semigroup, Show)

empty :: Env v
empty = Env Map.empty

null :: Env v -> Bool
null = Map.null . unEnv

lookup :: Ord v => v -> Env v -> Maybe Value
lookup n = Map.lookup n . unEnv

insert :: Ord v => v -> Value -> Env v -> Env v
insert n v = Env . Map.insert n v . unEnv

union :: Ord v => Env v -> Env v -> Env v
union (Env e1) (Env e2) = Env (Map.union e1 e2)

filter :: (v -> Value -> Bool) -> Env v -> Env v
filter f = Env . Map.filterWithKey f . unEnv

instance (Ord v, Pretty v) => Pretty (Env v) where
  pretty = tabulate2 (space <> pretty "=" <> space) . map (green . pretty *** nest 2 . align . group . pretty) . Map.toList . unEnv

instance (Ord v, Pretty v) => PrettyPrec (Env v)
