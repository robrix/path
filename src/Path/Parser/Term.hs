{-# LANGUAGE FlexibleContexts, FlexibleInstances, LambdaCase #-}
module Path.Parser.Term where

import Control.Applicative (Alternative(..), (<**>))
import Path.Name hiding (name)
import Path.Parser as Parser
import Path.Plicity
import Path.Parser.Mixfix
import Path.Span (unSpanned)
import Path.Surface (Surface)
import qualified Path.Surface as Surface
import Path.Syntax
import Path.Term
import Text.Trifecta hiding ((:@))

type', var, term, application, piType, functionType, lambda, atom :: DeltaParsing m => m (Spanned (Term Surface User))

term = functionType

application = foldl app <$> atom <*> many (spanned (plicit term atom)) <?> "function application"
  where app f@(_ :~ s1) (a :~ s2) = (f Surface.$$ a) :~ (s1 <> s2)

type' = spanned (Surface.type' <$ keyword "Type")

piType = spanned (do
  p :< (v, ty) <- plicit binding (parens binding) <* op "->"
  Surface.pi (p :< named (Just v) v ::: ty) <$> functionType) <?> "dependent function type"
  where binding = ((,) <$> name <* colon <*> term)

functionType = spanned (application <**> (flip (Surface.-->) <$ op "->" <*> functionType <|> pure unSpanned))
           <|> piType

var = spanned (pure <$> name <?> "variable")

lambda = (do
  vs <- op "\\" *> some pattern <* dot
  foldr bind term vs) <?> "lambda"
  where pattern = spanned (plicit binding binding) <?> "pattern"
        binding = Just <$> name <|> Nothing <$ token (string "_")
        bind v vv = wrap v <$> spanned vv
        wrap (a :~ v1) (b :~ v2) = Surface.lam' a b :~ (v1 <> v2)

atom = var <|> type' <|> lambda <|> try (parens term)

plicit :: TokenParsing m => m a -> m a -> m (Plicit a)
plicit a b = (Im :<) <$> braces a <|> (Ex :<) <$> b

name :: (Monad m, TokenParsing m) => m User
name =       (Id <$> identifier <?> "name")
     <|> try (Op <$> parens operator <?> "operator name")
