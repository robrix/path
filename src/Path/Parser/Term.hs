{-# LANGUAGE FlexibleInstances, LambdaCase #-}
module Path.Parser.Term where

import Control.Applicative (Alternative(..), (<**>))
import Data.Maybe (fromMaybe)
import Path.Name
import Path.Parser as Parser
import Path.Plicity
import Path.Parser.Mixfix
import Path.Surface
import Path.Usage
import Text.Trifecta
import Text.Parser.Token.Highlight

type', var, hole, term, application, piType, functionType, lambda, atom :: DeltaParsing m => m Surface

term = functionType

ann :: DeltaParsing m => m Surface -> m Surface
ann = fmap respan . spanned
  where respan (f :~ a) = Ann a f

application = atom `chainl1` pure (:$) <?> "function application"

type' = ann (Type <$ keyword "Type")

piType = ann (do
  (p, (v, mult, ty)) <- plicity ((,,) <$> name <* colon <*> optional multiplicity <*> term) <* op "->"
  (Pi (Just v) p (fromMaybe (case p of { Ex -> More ; Im -> Zero }) mult) ty) <$> functionType) <?> "dependent function type"
  where plicity m = (,) Im <$> braces m
                <|> (,) Ex <$> parens m

functionType = (,) <$> multiplicity <*> application <**> (flip (:->) <$ op "->" <*> functionType)
                <|> application <**> (arrow <$ op "->" <*> functionType <|> pure id)
                <|> piType
          where arrow t' t = (More, t) :-> t'

var = ann (Var <$> name <?> "variable")

lambda = ann (do
  vs <- op "\\" *> patterns <* dot
  bind vs) <?> "lambda"
  where pattern = spanned (Just <$> name <|> Nothing <$ token (string "_")) <?> "pattern"
        patterns = (:) <$> pattern <*> (patterns <|> pure [])
        bind [] = term
        bind (v:vv) = wrap v <$> spanned (bind vv)
          where wrap (a :~ v1) (b :~ v2) = Ann (v1 <> v2) (Lam a b)

hole = ann (Hole . Id <$> ident (IdentifierStyle "hole" (char '?') (alphaNum <|> char '\'') reservedWords Identifier ReservedIdentifier))

atom = var <|> type' <|> lambda <|> try (parens term) <|> hole

multiplicity :: (Monad m, TokenParsing m) => m Usage
multiplicity = Zero <$ keyword "0" <|> One <$ keyword "1"

name :: (Monad m, TokenParsing m) => m User
name =       (Id <$> identifier <?> "name")
     <|> try (Op <$> parens operator <?> "operator name")
