{-# LANGUAGE FlexibleContexts, LambdaCase #-}
module Path.Solver where

import Control.Effect
import Control.Effect.Error
import qualified Data.Set as Set
import Path.Error
import Path.Type
import Text.Trifecta.Rendering (Span)

simplify :: (Carrier sig m, Member (Error ElabError) sig, Monad m) => Span -> Equation -> m (Set.Set Equation)
simplify span = \case
  tm1 ::: ty1 :===: tm2 ::: ty2 | ty1 == ty2, tm1 == tm2 -> pure Set.empty
  q -> throwError (ElabError span mempty (TypeMismatch q))
