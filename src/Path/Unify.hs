module Path.Unify where

import Path.Context
import Path.Name
import Path.Value

unifiesWith :: Applicative m => Type QName -> Type QName -> m Bool
unifiesWith t1 t2 = pure (t1 `aeq` t2)
