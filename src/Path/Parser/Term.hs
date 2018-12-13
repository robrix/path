{-# LANGUAGE FlexibleInstances #-}
module Path.Parser.Term where

import Control.Applicative (Alternative(..), (<**>))
import Control.Monad.State
import Data.Maybe (fromMaybe)
import Path.Name
import Path.Parser as Parser
import qualified Path.Surface as Surface
import Path.Term hiding (ann)
import Path.Usage
import Text.Trifecta
import Text.Trifecta.Indentation

type', var :: DeltaParsing m => m (Term (Surface.Surface Name) Span)
term, application, annotation, piType, functionType, forAll, lambda, atom :: (DeltaParsing m, MonadFresh m) => m (Term (Surface.Surface Name) Span)

term = annotation

ann :: DeltaParsing m => m (f (Term f Span)) -> m (Term f Span)
ann = fmap respan . spanned
  where respan (f :~ a) = In f a

reann :: DeltaParsing m => m (Term f Span) -> m (Term f Span)
reann = fmap respan . spanned
  where respan (In f _ :~ a) = In f a


application = atom `chainl1` pure (Surface.#) <?> "function application"

type' = ann (Surface.typeT <$ keyword "Type")

forAll = reann (do
  (v, ty) <- op "∀" *> binding <* dot
  Surface.forAll (v, ty) <$> functionType) <?> "universally quantified type"
  where binding = (,) <$> name <* colon <*> term

piType = reann (do
  (v, mult, ty) <- braces ((,,) <$> name <* colon <*> optional multiplicity <*> term) <* op "->"
  ((v, fromMaybe More mult, ty) Surface.-->) <$> functionType) <?> "dependent function type"

annotation = functionType `chainr1` ((Surface..:) <$ op ":")

functionType = (,,) <$> freshName <*> multiplicity <*> application <**> (flip (Surface.-->) <$ op "->" <*> functionType)
                <|> application <**> (arrow <$ op "->" <*> freshName <*> functionType <|> pure id)
                <|> piType
                <|> forAll
          where arrow v t' t = (v, More, t) Surface.--> t'

var = ann (Surface.var <$> name <?> "variable")

lambda = reann (do
  vs <- op "\\" *> some pattern <* dot
  bind vs) <?> "lambda"
  where pattern = spanned (name <|> token (string "_") *> freshName) <?> "pattern"
        bind [] = term
        bind ((v :~ a):vv) = Surface.lam (v, a) <$> bind vv

atom = var <|> type' <|> lambda <|> parens term

multiplicity :: (Monad m, TokenParsing m) => m Usage
multiplicity = Zero <$ keyword "0" <|> One <$ keyword "1"

name :: (Monad m, TokenParsing m) => m Name
name = Name <$> identifier <?> "name"


class Monad m => MonadFresh m where
  freshName :: m Name

mkName :: Int -> Name
mkName i = Name ('\'' : c : replicate r c)
  where alphabet = ['a'..'z']
        (q, r) = i `divMod` 26
        c = alphabet !! q

instance Monad m => MonadFresh (StateT Int m) where
  freshName = do
    n <- gets mkName
    n <$ modify succ

instance MonadFresh Parser.Parser where
  freshName = Parser.Parser freshName

instance MonadFresh m => MonadFresh (IndentationParserT Char m) where
  freshName = lift freshName
