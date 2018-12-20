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
import Text.Parser.Token.Highlight

type', var, hole :: DeltaParsing m => m (Term (Surface.Surface Name) Span)
term, application, annotation, piType, functionType, forAll, lambda, atom :: (DeltaParsing m, MonadFresh m) => m (Term (Surface.Surface Name) Span)

term = annotation

ann :: DeltaParsing m => m (f (Term f Span)) -> m (Term f Span)
ann = fmap respan . spanned
  where respan (f :~ a) = In f a

reann :: DeltaParsing m => m (Term f Span) -> m (Term f Span)
reann = fmap respan . spanned
  where respan (In f _ :~ a) = In f a


application = atom `chainl1` pure (Surface.#) <?> "function application"

type' = ann (Surface.Type <$ keyword "Type")

forAll = reann (do
  (v, ty) <- op "∀" *> binding <* dot
  Surface.forAll (v, ty) <$> functionType) <?> "universally quantified type"
  where binding = (,) <$> name <* colon <*> term

piType = reann (do
  (v, mult, ty) <- braces ((,,) <$> name <* colon <*> optional multiplicity <*> term) <* op "->"
  ((v, fromMaybe More mult, ty) Surface.-->) <$> functionType) <?> "dependent function type"

annotation = functionType `chainr1` ((Surface..:) <$ op ":")

functionType = (,,) <$ push <*> freshName <*> multiplicity <*> application <**> (flip (Surface.-->) <$ op "->" <*> functionType) <* pop
                <|> push *> application <**> (arrow <$ op "->" <*> freshName <*> functionType <|> pure id) <* pop
                <|> piType
                <|> forAll
          where arrow v t' t = (v, More, t) Surface.--> t'

var = ann (Surface.Var <$> name <?> "variable")

lambda = reann (do
  vs <- op "\\" *> patterns <* dot
  bind vs) <?> "lambda"
  where pattern = spanned (name <|> token (string "_") *> freshName) <?> "pattern"
        patterns = (:) <$ push <*> pattern <*> (patterns <|> pure []) <* pop
        bind [] = term
        bind ((v :~ a):vv) = Surface.lam (v, a) <$> bind vv

hole = ann (Surface.Hole . Name <$> ident (IdentifierStyle "hole" (char '?') (alphaNum <|> char '\'') reservedWords Identifier ReservedIdentifier))

atom = var <|> type' <|> lambda <|> parens term <|> hole

multiplicity :: (Monad m, TokenParsing m) => m Usage
multiplicity = Zero <$ keyword "0" <|> One <$ keyword "1"

name :: (Monad m, TokenParsing m) => m Name
name =       (Name <$> identifier <?> "name")
     <|> try (Name <$> parens operator <?> "operator name")


class Monad m => MonadFresh m where
  push :: m ()
  pop :: m ()
  freshName :: m Name

instance MonadFresh Parser.Parser where
  push = Parser.Parser (modify succ)
  pop = Parser.Parser (modify pred)
  freshName = Parser.Parser (gets Gensym)

instance MonadFresh m => MonadFresh (IndentationParserT t m) where
  push = lift push
  pop = lift pop
  freshName = lift freshName
