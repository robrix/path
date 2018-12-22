module Path.Parser.Mixfix where

import Control.Applicative (Alternative(..))
import Data.List.NonEmpty (NonEmpty(..), some1)
import Text.Parser.Token.Highlight
import Text.Trifecta

data Operator
  = Prefix (NonEmpty String)
  | Postfix (NonEmpty String)
  | Infix (NonEmpty String)
  | Closed String (NonEmpty String)

betweenOp :: String -> String -> Operator
betweenOp a b = Closed a (b :| [])

parensOp :: Operator
parensOp = betweenOp "(" ")"

ifthenelse :: Operator
ifthenelse = Prefix ("if" :| [ "then", "else" ])


placeholder :: TokenParsing m => m ()
placeholder = () <$ token (char '_')


prefix, postfix :: (Monad m, TokenParsing m) => m Operator

prefix = Prefix <$> some1 (fragment <* placeholder)
postfix = Postfix <$> some1 (placeholder *> fragment)


fragment :: (Monad m, TokenParsing m) => m String
fragment = ident (IdentifierStyle "fragment" letter (alphaNum <|> char '\'') mempty Identifier ReservedIdentifier)
