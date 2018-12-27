{-# LANGUAGE FlexibleInstances #-}
module Path.Parser.Term where

import Control.Applicative (Alternative(..), (<**>))
import Control.Monad.State
import Data.Maybe (fromMaybe)
import Path.Name
import Path.Parser as Parser
import Path.Parser.Mixfix
import qualified Path.Surface as Surface
import Path.Term hiding (ann)
import Path.Usage
import Text.Trifecta
import Text.Trifecta.Indentation
import Text.Parser.Token.Highlight

type', var, hole, implicit, term, application, piType, functionType, forAll, lambda, atom :: DeltaParsing m => m (Term (Surface.Surface (Maybe Name) Name) Span)

term = functionType

ann :: DeltaParsing m => m (f (Term f Span)) -> m (Term f Span)
ann = fmap respan . spanned
  where respan (f :~ a) = In f a

reann :: DeltaParsing m => m (Term f Span) -> m (Term f Span)
reann = fmap respan . spanned
  where respan (In f _ :~ a) = In f a


application = atom `chainl1` pure (Surface.#) <?> "function application"

type' = ann (Surface.type' <$ keyword "Type")

forAll = reann (do
  (v, ty) <- op "∀" *> binding <* dot
  Surface.forAll (v, ty) <$> functionType) <?> "universally quantified type"
  where binding = (,) . Just <$> name <* colon <*> term

piType = reann (do
  (v, mult, ty) <- braces ((,,) . Just <$> name <* colon <*> optional multiplicity <*> term) <* op "->"
  (Surface.piType (v, fromMaybe More mult, ty)) <$> functionType) <?> "dependent function type"

functionType = (,) <$> multiplicity <*> application <**> (flip (Surface.-->) <$ op "->" <*> functionType)
                <|> application <**> (arrow <$ op "->" <*> functionType <|> pure id)
                <|> piType
                <|> forAll
          where arrow t' t = (More, t) Surface.--> t'

var = ann (Surface.var <$> name <?> "variable")

lambda = reann (do
  vs <- op "\\" *> patterns <* dot
  bind vs) <?> "lambda"
  where pattern = spanned (Just <$> name <|> Nothing <$ token (string "_")) <?> "pattern"
        patterns = (:) <$> pattern <*> (patterns <|> pure [])
        bind [] = term
        bind ((v :~ a):vv) = Surface.lam (v, a) <$> bind vv

hole = ann (Surface.hole . Name <$> ident (IdentifierStyle "hole" (char '?') (alphaNum <|> char '\'') reservedWords Identifier ReservedIdentifier))

implicit = ann (Surface.implicit <$ token (char '_'))

atom = var <|> type' <|> lambda <|> parens term <|> hole <|> implicit

multiplicity :: (Monad m, TokenParsing m) => m Usage
multiplicity = Zero <$ keyword "0" <|> One <$ keyword "1"

name :: (Monad m, TokenParsing m) => m Name
name =       (Name <$> identifier <?> "name")
     <|> try (Op <$> parens operator <?> "operator name")


class Monad m => MonadFresh m where
  push :: m ()
  pop :: m ()
  freshName :: m Name

instance MonadFresh Parser.Inner where
  push = Parser.Inner (modify succ)
  pop = Parser.Inner (modify pred)
  freshName = Parser.Inner (gets Gensym)

instance MonadFresh m => MonadFresh (IndentationParserT t m) where
  push = lift push
  pop = lift pop
  freshName = lift freshName
