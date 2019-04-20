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

type', var, hole, term, application, piType, functionType, lambda, atom :: DeltaParsing m => m (Spanned Surface)

term = functionType

application = atom <**> (flip (foldl wrap) <$> many (plicit atom)) <?> "function application"
  where wrap f@(_ :~ s1) a@(_ :< (_ :~ s2)) = (f :$ a) :~ (s1 <> s2)

type' = spanned (Type <$ keyword "Type")

piType = spanned (do
  p :< (v, mult, ty) <- plicity ((,,) <$> name <* colon <*> optional multiplicity <*> term) <* op "->"
  Pi (p :< (Just v, fromMaybe (case p of { Ex -> More ; Im -> Zero }) mult, ty)) <$> functionType) <?> "dependent function type"
  where plicity m = (Im :<) <$> braces m
                <|> (Ex :<) <$> parens m

functionType = spanned ((,) <$> multiplicity <*> application <**> (flip (:->) <$ op "->" <*> functionType))
                <|> application <**> (arrow <$ op "->" <*> functionType <|> pure id)
                <|> piType
          where arrow t'@(_ :~ s2) t@(_ :~ s1) = ((More, t) :-> t') :~ (s1 <> s2)

var = spanned (Var <$> name <?> "variable")

lambda = (do
  vs <- op "\\" *> some pattern <* dot
  bind vs) <?> "lambda"
  where pattern = spanned (plicit (Just <$> name <|> Nothing <$ token (string "_"))) <?> "pattern"
        bind [] = term
        bind (v:vv) = wrap v <$> spanned (bind vv)
          where wrap (a :~ v1) (b :~ v2) = Lam a b :~ (v1 <> v2)

hole = spanned (Hole . Id <$> ident (IdentifierStyle "hole" (char '?') (alphaNum <|> char '\'') reservedWords Identifier ReservedIdentifier))

atom = var <|> type' <|> lambda <|> try (parens term) <|> hole

multiplicity :: (Monad m, TokenParsing m) => m Usage
multiplicity = Zero <$ keyword "0" <|> One <$ keyword "1"

plicit :: TokenParsing m => m a -> m (Plicit a)
plicit a = (Im :<) <$> braces a <|> (Ex :<) <$> a

name :: (Monad m, TokenParsing m) => m User
name =       (Id <$> identifier <?> "name")
     <|> try (Op <$> parens operator <?> "operator name")
