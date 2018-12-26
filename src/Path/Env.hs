{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Path.Env where

import Control.Arrow ((***))
import qualified Data.Map as Map
import Path.Name
import Path.Pretty
import Path.Value
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

newtype Env = Env { unEnv :: Map.Map QName Value }
  deriving (Eq, Monoid, Ord, Semigroup, Show)

empty :: Env
empty = Env Map.empty

null :: Env -> Bool
null = Map.null . unEnv

lookup :: QName -> Env -> Maybe Value
lookup n = Map.lookup n . unEnv

insert :: QName -> Value -> Env -> Env
insert n v = Env . Map.insert n v . unEnv

union :: Env -> Env -> Env
union (Env e1) (Env e2) = Env (Map.union e1 e2)

filter :: (QName -> Value -> Bool) -> Env -> Env
filter f = Env . Map.filterWithKey f . unEnv

instance Pretty Env where
  pretty = tabulate2 (space <> pretty "=" <> space) . map (green . pretty *** nest 2 . align . group . pretty) . Map.toList . unEnv

instance PrettyPrec Env
