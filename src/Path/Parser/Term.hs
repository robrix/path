{-# LANGUAGE FlexibleInstances, LambdaCase #-}
module Path.Parser.Term where

import Control.Applicative (Alternative(..), (<**>))
import Data.Maybe (fromMaybe)
import Path.Name hiding (name)
import Path.Parser as Parser
import Path.Plicity
import Path.Parser.Mixfix
import Path.Surface (Surface)
import qualified Path.Surface as Surface
import Path.Usage
import Text.Trifecta hiding ((:@))
import Text.Parser.Token.Highlight

type', var, hole, term, application, piType, functionType, lambda, atom :: DeltaParsing m => m (Spanned (Surface User))

term = functionType

application = foldl app <$> atom <*> many (spanned (plicit term atom)) <?> "function application"
  where app f@(_ :~ s1) (a :~ s2) = (f Surface.$$ a) :~ (s1 <> s2)

type' = spanned (Surface.type' <$ keyword "Type")

piType = spanned (do
  p :< (v, mult, ty) <- plicit binding (parens binding) <* op "->"
  Surface.pi (p :< (v, v) ::: fromMaybe (case p of { Ex -> More ; Im -> Zero }) mult :@ ty) <$> functionType) <?> "dependent function type"
  where binding = ((,,) <$> name <* colon <*> optional multiplicity <*> term)

functionType = spanned ((:@) <$> multiplicity <*> application <**> (flip (Surface.-->) <$ op "->" <*> functionType))
                <|> application <**> (arrow <$ op "->" <*> functionType <|> pure id)
                <|> piType
          where arrow t'@(_ :~ s2) t@(_ :~ s1) = (More :@ t Surface.--> t') :~ (s1 <> s2)

var = spanned (pure <$> name <?> "variable")

lambda = (do
  vs <- op "\\" *> some pattern <* dot
  bind vs) <?> "lambda"
  where pattern = spanned (plicit binding binding) <?> "pattern"
        binding = name <|> Unused <$ token (string "_")
        bind [] = term
        bind (v:vv) = wrap v <$> spanned (bind vv)
        wrap ((p :< a) :~ v1) (b :~ v2) = Surface.lam (p :< (a, a)) b :~ (v1 <> v2)

hole = spanned (Surface.hole <$ char '?' <*> optional (ident (IdentifierStyle "hole" letter (alphaNum <|> char '\'') reservedWords Identifier ReservedIdentifier)))

atom = var <|> type' <|> lambda <|> try (parens term) <|> hole

multiplicity :: (Monad m, TokenParsing m) => m Usage
multiplicity = Zero <$ keyword "0" <|> One <$ keyword "1"

plicit :: TokenParsing m => m a -> m a -> m (Plicit a)
plicit a b = (Im :<) <$> braces a <|> (Ex :<) <$> b

name :: (Monad m, TokenParsing m) => m User
name =       (Id <$> identifier <?> "name")
     <|> try (Op <$> parens operator <?> "operator name")
