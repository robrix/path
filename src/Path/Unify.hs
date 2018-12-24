{-# LANGUAGE DeriveTraversable, FlexibleContexts #-}
module Path.Unify where

import Control.Effect
import Control.Effect.Fresh
import Control.Effect.Reader
import Control.Effect.State
import qualified Path.Context as Context
import Path.Core
import Path.Name
import Path.Subst
import qualified Path.Term as Term

data Back a = Nil | Back a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)


type Term = Term.Term (Core QName) ()
type Type = Context.Type QName

data Twin = Only | TwinL | TwinR
  deriving (Eq, Ord, Show)

data Equation = (Term, Type) :==: (Term, Type)
  deriving (Eq, Ord, Show)

sym :: Equation -> Equation
sym (s :==: t) = t :==: s

data Param = P Type | Type :++: Type
  deriving (Eq, Ord, Show)

type Params = Back (QName, Param)

data Dec a = Hole | Defn a
  deriving (Eq, Ord, Show)

data Entry
  = E QName Type (Dec Term)
  | Q Status Problem
  deriving (Eq, Ord, Show)

data Status = Blocked | Active
  deriving (Eq, Ord, Show)

data Problem
  = Unify Equation
  | All Param QName Problem
  deriving (Eq, Ord, Show)


type ContextL = Back Entry
type ContextR = [Either (Subst QName Term) Entry]

popL :: (Carrier sig m, Member (State ContextL) sig, Monad m) => m Entry
popL = do
  entries <- get
  case entries of
    es :> e -> e <$ put es
    Nil     -> error "popL: empty context"

pushL :: (Carrier sig m, Member (State ContextL) sig, Monad m) => Entry -> m ()
pushL e = modify (:> e)


popR :: (Carrier sig m, Member (State ContextR) sig, Monad m) => m (Maybe (Either (Subst QName Term) Entry))
popR = do
  entries <- get
  case entries of
    e : es -> Just e <$ put es
    []     -> pure Nothing

pushR :: (Carrier sig m, Member (State ContextR) sig, Monad m) => Either (Subst QName Term) Entry -> m ()
pushR e = modify (e:)

lookupMeta :: (Carrier sig m, Member (State ContextL) sig, Monad m) => QName -> m Type
lookupMeta x = get >>= go
  where go (_   :> E y _T _) | x == y = pure _T
        go (mcx :> _)                 = go mcx
        go Nil                        = error $ "lookupMeta: missing " <> show x


askParams :: (Carrier sig m, Member (Reader Params) sig) => m Params
askParams = ask

localParams :: (Carrier sig m, Member (Reader Params) sig) => (Params -> Params) -> m a -> m a
localParams = local

lookupVar :: (Carrier sig m, Member (Reader Params) sig, Monad m) => QName -> Twin -> m Type
lookupVar x w = ask >>= go w
  where go Only  (_ :> (y, P t))      | x == y = return t
        go TwinL (_ :> (y, s :++: _)) | x == y = return s
        go TwinR (_ :> (y, _ :++: t)) | x == y = return t
        go w     (c :> _)                      = go w c
        go _     Nil                           = error $ "lookupVar: missing " <> show x -- FIXME: free variable error or something?


freshName :: (Applicative m, Carrier sig m, Member Fresh sig, Member (Reader ModuleName) sig) => m QName
freshName = mk <$> ask <*> fresh
  where mk m i = m :.: Gensym i


postpone :: (Carrier sig m, Member (Reader Params) sig, Member (State ContextR) sig, Monad m) => Status -> Problem -> m ()
postpone s p = ask >>= pushR . Right . Q s . wrapProb p
  where wrapProb :: Problem -> Params -> Problem
        wrapProb = foldr (\ (x, e) p -> All e x p)

active, block :: (Carrier sig m, Member (Reader Params) sig, Member (State ContextR) sig, Monad m) => Problem -> m ()
active  = postpone Active
block   = postpone Blocked
