module Path.Parser.Mixfix where

import Control.Applicative (Alternative(..))
import Data.Char (isPunctuation, isSymbol)
import Data.List.NonEmpty (NonEmpty(..), some1)
import Text.Parser.Token.Highlight
import Text.Trifecta as Trifecta

data Operator
  = Prefix (NonEmpty String)
  | Postfix (NonEmpty String)
  | Infix (NonEmpty String)
  | Closed String (NonEmpty String)
  deriving (Eq, Ord, Show)

betweenOp :: String -> String -> Operator
betweenOp a b = Closed a (b :| [])

parensOp :: Operator
parensOp = betweenOp "(" ")"

ifthenelse :: Operator
ifthenelse = Prefix ("if" :| [ "then", "else" ])


placeholder :: TokenParsing m => m ()
placeholder = () <$ token (char '_')


operator, infix', postfix, closed, prefix :: (Monad m, TokenParsing m) => m Operator

-- | Parse a mixfix operator.
--
-- >>> Trifecta.parseString operator mempty "_ ⊢ _ : _"
-- Success (Infix ("\8866" :| [":"]))
-- >>> Trifecta.parseString operator mempty "_ [ _ ]"
-- Success (Postfix ("[" :| ["]"]))
-- >>> Trifecta.parseString operator mempty "| _ |"
-- Success (Closed "|" ("|" :| []))
-- >>> Trifecta.parseString operator mempty "if _ then _ else _"
-- Success (Prefix ("if" :| ["then","else"]))
operator = try infix' <|> postfix <|> try closed <|> prefix

infix' = Infix <$ placeholder <*> (fragment `endByNonEmpty` placeholder)
postfix = Postfix <$> some1 (placeholder *> fragment)
closed = Closed <$> fragment <*> some1 (placeholder *> fragment)
prefix = Prefix <$> some1 (fragment <* placeholder)


-- | Parse a name fragment.
--
-- >>> foldResult (const Nothing) Just (Trifecta.parseString fragment mempty "_")
-- Nothing
fragment :: (Monad m, TokenParsing m) => m String
fragment = ident (IdentifierStyle "fragment" (letter <|> satisfy isOperator) (alphaNum <|> char '\'' <|> satisfy isOperator) mempty Identifier ReservedIdentifier)
  where isOperator '_' = False
        isOperator c   = isPunctuation c || isSymbol c
