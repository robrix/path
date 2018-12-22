module Path.Parser.Mixfix where

import Control.Applicative (Alternative(..), (<**>))
import Data.Char (isPunctuation, isSymbol)
import Data.List.NonEmpty (NonEmpty(..), some1)
import Text.Parser.Token.Highlight
import Text.Trifecta as Trifecta

data Operator
  = Prefix (NonEmpty String)
  | Postfix (NonEmpty String)
  | Infix (NonEmpty String)
  | Closed (NonEmpty String) String
  deriving (Eq, Ord, Show)

betweenOp :: String -> String -> Operator
betweenOp a b = Closed (a :| []) b

parensOp :: Operator
parensOp = betweenOp "(" ")"

ifthenelse :: Operator
ifthenelse = Prefix ("if" :| [ "then", "else" ])


placeholder :: TokenParsing m => m ()
placeholder = () <$ token (char '_')


operator, inOrPostfix, closed, prefix :: (Monad m, TokenParsing m) => m Operator

-- | Parse a mixfix operator.
--
-- >>> Trifecta.parseString operator mempty "_ ⊢ _ : _"
-- Success (Infix ("\8866" :| [":"]))
-- >>> Trifecta.parseString operator mempty "_ [ _ ]"
-- Success (Postfix ("[" :| ["]"]))
-- >>> Trifecta.parseString operator mempty "| _ |"
-- Success (Closed ("|" :| []) "|")
-- >>> Trifecta.parseString operator mempty "if _ then _ else _"
-- Success (Prefix ("if" :| ["then","else"]))
operator = inOrPostfix <|> try closed <|> prefix

inOrPostfix = some1 (try (placeholder *> fragment)) <**> (Infix <$ placeholder <|> pure Postfix)
closed = Closed <$> some1 (try (fragment <* placeholder)) <*> fragment
prefix = Prefix <$> some1 (fragment <* placeholder)


-- | Parse a name fragment.
--
-- >>> foldResult (const Nothing) Just (Trifecta.parseString fragment mempty "_")
-- Nothing
fragment :: (Monad m, TokenParsing m) => m String
fragment = ident (IdentifierStyle "fragment" (letter <|> satisfy isOperator) (alphaNum <|> char '\'' <|> satisfy isOperator) mempty Identifier ReservedIdentifier)
  where isOperator '_' = False
        isOperator c   = isPunctuation c || isSymbol c
