{-# LANGUAGE DeriveFunctor #-}
module Path.Eval where

import Data.Bifunctor (first)
import Data.Function (on)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Path.Core
import Path.FreeVariables
import Path.Name
import Path.Pretty
import Path.Term
import Path.Usage
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

data Value
  = VLam (Maybe String) (Value -> Value)
  | VType
  | VPi (Maybe String) Usage Value (Value -> Value)
  | VNeutral (Neutral String)

instance Eq Value where
  (==) = (==) `on` quote

instance Ord Value where
  compare = compare `on` quote

instance Show Value where
  showsPrec d = showsPrec d . quote

instance PrettyPrec Value where
  prettyPrec d = prettyPrec d . hoist (first Name) . quote

instance Pretty Value where
  pretty = prettyPrec 0

instance FreeVariables Value where
  fvs = fvs . hoist (first Name) . quote

vfree :: String -> Value
vfree = VNeutral . NFree

data Neutral v
  = NFree v
  | NApp (Neutral v) Value
  deriving (Eq, Functor, Ord, Show)

quote :: Value -> Term (Core String) ()
quote VType = In Type ()
quote (VLam v f) = In (Lam v (quote (f (vfree (fromMaybe "_" v))))) ()
quote (VPi v e t f) = In (Pi v e (quote t) (quote (f (vfree (fromMaybe "_" v))))) ()
quote (VNeutral n) = quoteN n

quoteN :: Neutral String -> Term (Core String) ()
quoteN (NFree s) = In (Var s) ()
quoteN (NApp n a) = In (quoteN n :@ quote a) ()


type Env = Map.Map String Value

eval :: Term (Core Name) a -> Env -> Value
eval (In (Var n) _) d = fromMaybe (vfree (getName n)) (Map.lookup (getName n) d)
eval (In (Lam n b) _) d = VLam (getName <$> n) (eval b . maybe const (flip . Map.insert . getName) n d)
eval (In (f :@ a) _) d = eval f d `vapp` eval a d
eval (In Type _) _ = VType
eval (In (Pi n e ty b) _) d = VPi (getName <$> n) e (eval ty d) (eval b . maybe const (flip . Map.insert . getName) n d)

vapp :: Value -> Value -> Value
vapp (VLam _ f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)
vapp f a = error ("illegal application of " <> show f <> " to " <> show a)
