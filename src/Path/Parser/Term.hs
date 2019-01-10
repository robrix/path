{-# LANGUAGE FlexibleInstances #-}
module Path.Parser.Term where

import Control.Applicative (Alternative(..), (<**>))
import Data.Maybe (fromMaybe)
import Path.Name
import Path.Parser as Parser
import Path.Plicity
import Path.Parser.Mixfix
import qualified Path.Surface as Surface
import Path.Term hiding (ann)
import Path.Usage
import Text.Trifecta
import Text.Parser.Token.Highlight

type', var, hole, term, application, piType, functionType, lambda, atom :: DeltaParsing m => m (Term (Surface.Surface (Maybe UName) UName))

term = functionType

ann :: DeltaParsing m => m (f (Term f)) -> m (Term f)
ann = fmap respan . spanned
  where respan (f :~ a) = In f a

reann :: DeltaParsing m => m (Term f) -> m (Term f)
reann = fmap respan . spanned
  where respan (In f _ :~ a) = In f a


application = atom `chainl1` pure (Surface.$$) <?> "function application"

type' = ann (Surface.type' <$ keyword "Type")

piType = reann (do
  (p, (v, mult, ty)) <- plicity ((,,) . Just <$> name <* colon <*> optional multiplicity <*> term) <* op "->"
  (Surface.piType (v, p, fromMaybe (case p of { Ex -> More ; Im -> Zero }) mult, ty)) <$> functionType) <?> "dependent function type"
  where plicity m = (,) Im <$> braces m
                <|> (,) Ex <$> parens m

functionType = (,) <$> multiplicity <*> application <**> (flip (Surface.-->) <$ op "->" <*> functionType)
                <|> application <**> (arrow <$ op "->" <*> functionType <|> pure id)
                <|> piType
          where arrow t' t = (More, t) Surface.--> t'

var = ann (Surface.var <$> name <?> "variable")

lambda = reann (do
  vs <- op "\\" *> patterns <* dot
  bind vs) <?> "lambda"
  where pattern = spanned (Just <$> name <|> Nothing <$ token (string "_")) <?> "pattern"
        patterns = (:) <$> pattern <*> (patterns <|> pure [])
        bind [] = term
        bind ((v :~ a):vv) = Surface.lam (v, a) <$> bind vv

hole = ann (Surface.hole . UName <$> ident (IdentifierStyle "hole" (char '?') (alphaNum <|> char '\'') reservedWords Identifier ReservedIdentifier))

atom = var <|> type' <|> lambda <|> try (parens term) <|> hole

multiplicity :: (Monad m, TokenParsing m) => m Usage
multiplicity = Zero <$ keyword "0" <|> One <$ keyword "1"

name :: (Monad m, TokenParsing m) => m UName
name =       (UName <$> identifier <?> "name")
     <|> try (UOp <$> parens operator <?> "operator name")
