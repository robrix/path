{-# LANGUAGE FlexibleContexts, FlexibleInstances, LambdaCase #-}
module Path.Parser.Term where

import Control.Applicative (Alternative(..), (<**>))
import Control.Effect.Parser
import Control.Effect.Reader
import Path.Name
import Path.Parser as Parser
import Path.Plicity
import Path.Span (Spanned(..), unSpanned)
import Path.Surface (Surface)
import qualified Path.Surface as Surface
import Path.Syntax
import Text.Parser.Char
import Text.Parser.Combinators
import Text.Parser.Token

type', var, term, application, piType, functionType, lambda, atom :: (Has Parser sig m, Has (Reader Lines) sig m, Has (Reader Path) sig m, TokenParsing m) => m (Spanned (Surface User))

term = functionType

application = foldl app <$> atom <*> many (spanned (plicit term atom)) <?> "function application"
  where app f@(_ :~ s1) (a :~ s2) = (f Surface.:$ a) :~ (s1 <> s2)

type' = spanned (Surface.Type <$ keyword "Type")

piType = spanned (do
  p :< (v, ty) <- plicit binding (parens binding) <* op "->"
  Surface.pi (p :< named (Just v) v ::: ty) <$> functionType) <?> "dependent function type"
  where binding = ((,) <$> name <* colon <*> term)

functionType = spanned (application <**> (flip (Surface.-->) <$ op "->" <*> functionType <|> pure unSpanned))
           <|> piType

var = spanned (pure <$> name <?> "variable")

lambda = spanned (unSpanned <$ op "\\" <*> recur) <?> "lambda"
  where recur = spanned (Surface.lam' <$> pattern <*> (recur <|> dot *> term)) <?> "lambda"
        pattern = plicit binding binding <?> "pattern"
        binding = Just <$> name <|> Nothing <$ token (string "_")

atom = var <|> type' <|> lambda <|> try (parens term)

plicit :: TokenParsing m => m a -> m a -> m (Plicit a)
plicit a b = (Im :<) <$> braces a <|> (Ex :<) <$> b

name :: (Monad m, TokenParsing m) => m User
name = identifier <?> "name"
