module Path.Parser.Term where

import Control.Applicative (Alternative(..), (<**>))
import Data.List (find)
import Data.Maybe (fromMaybe)
import Path.Parser
import qualified Path.Surface as Surface
import Path.Term hiding (ann)
import Path.Usage
import Text.Trifecta

globalTerm, type' :: DeltaParsing m => m (Term Surface.Surface Span)
globalTerm = term []

term, application, annotation, piType, functionType, forAll, var, lambda, atom :: DeltaParsing m => [String] -> m (Term Surface.Surface Span)

term = annotation

ann :: DeltaParsing m => m (f (Term f Span)) -> m (Term f Span)
ann = fmap respan . spanned
  where respan (f :~ a) = In f a

reann :: DeltaParsing m => m (Term f Span) -> m (Term f Span)
reann = fmap respan . spanned
  where respan (In f _ :~ a) = In f a


application vs = atom vs `chainl1` pure (Surface.#) <?> "function application"

type' = ann (Surface.typeT <$ keyword "Type")

forAll vs = reann (do
  (v, ty) <- op "∀" *> binding <* dot
  Surface.forAll (v, ty) <$> functionType (v : vs)) <?> "universally quantified type"
  where binding = (,) <$> identifier <* colon <*> term vs

piType vs = reann (do
  (v, mult, ty) <- braces ((,,) <$> identifier <* colon <*> optional multiplicity <*> term vs) <* op "->"
  ((v, fromMaybe More mult, ty) Surface.-->) <$> functionType (v : vs)) <?> "dependent function type"

annotation vs = functionType vs `chainr1` ((Surface..:) <$ op ":")

functionType vs = (,,) "_" <$> multiplicity <*> application vs <**> (flip (Surface.-->) <$ op "->" <*> functionType vs)
                <|> application vs <**> (flip arrow <$ op "->" <*> functionType vs <|> pure id)
                <|> piType vs
                <|> forAll vs
          where arrow = (Surface.-->) . (,,) "_" More

var vs = ann (toVar <$> identifier <?> "variable")
  where toVar n = maybe (Surface.global n) Surface.var (find (== n) vs)

lambda vs = reann (do
  vs' <- op "\\" *> some pattern <* dot
  bind vs' vs) <?> "lambda"
  where pattern = spanned (identifier <|> token (string "_")) <?> "pattern"
        bind [] vs = term vs
        bind ((v :~ a):vv) vs = Surface.lam (v, a) <$> bind vv (v:vs)

atom vs = var vs <|> type' <|> lambda vs <|> parens (term vs)

multiplicity :: (Monad m, TokenParsing m) => m Usage
multiplicity = Zero <$ keyword "0" <|> One <$ keyword "1"
