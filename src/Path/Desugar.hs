module Path.Desugar where

import Path.Core as Core
import Path.Name
import Path.Surface as Surface
import Path.Term
import Path.Usage

desugar :: Term (Surface QName) a
        -> Maybe (Term Core a)
desugar (In out span) = flip In span <$> case out of
  Surface.Var n -> pure (Core.Var n)
  Surface.Lam n b -> Core.Lam n <$> desugar b
  f Surface.:@ a -> (Core.:@) <$> desugar f <*> desugar a
  Surface.Type -> pure Core.Type
  Surface.Pi n u t b -> Core.Pi n u <$> desugar t <*> desugar b
  Surface.ForAll n t b -> Core.Pi n Zero <$> desugar t <*> desugar b
  Surface.Hole _ -> Nothing
  Surface.Implicit -> Nothing
