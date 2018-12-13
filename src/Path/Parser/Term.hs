module Path.Parser.Term where

import Control.Applicative (Alternative(..), (<**>))
import Data.Maybe (fromMaybe)
import Path.Name
import Path.Parser
import qualified Path.Surface as Surface
import Path.Term hiding (ann)
import Path.Usage
import Text.Trifecta

term, application, type', annotation, piType, functionType, forAll, var, lambda, atom :: DeltaParsing m => m (Term (Surface.Surface Name) Span)

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
  Surface.forAll (Just v, ty) <$> functionType) <?> "universally quantified type"
  where binding = (,) <$> name <* colon <*> term

piType = reann (do
  (v, mult, ty) <- braces ((,,) <$> name <* colon <*> optional multiplicity <*> term) <* op "->"
  ((Just v, fromMaybe More mult, ty) Surface.-->) <$> functionType) <?> "dependent function type"

annotation = functionType `chainr1` ((Surface..:) <$ op ":")

functionType = (,,) Nothing <$> multiplicity <*> application <**> (flip (Surface.-->) <$ op "->" <*> functionType)
                <|> application <**> (flip arrow <$ op "->" <*> functionType <|> pure id)
                <|> piType
                <|> forAll
          where arrow = (Surface.-->) . (,,) Nothing More

var = ann (Surface.var <$> name <?> "variable")

lambda = reann (do
  vs <- op "\\" *> some pattern <* dot
  bind vs) <?> "lambda"
  where pattern = spanned (Just <$> name <|> Nothing <$ token (string "_")) <?> "pattern"
        bind [] = term
        bind ((v :~ a):vv) = Surface.lam (v, a) <$> bind vv

atom = var <|> type' <|> lambda <|> parens term

multiplicity :: (Monad m, TokenParsing m) => m Usage
multiplicity = Zero <$ keyword "0" <|> One <$ keyword "1"

name :: (Monad m, TokenParsing m) => m Name
name = Name <$> identifier <?> "name"


class MonadFresh m where
  freshName :: m Name
