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


operator, prefix, postfix, infix', closed :: (Monad m, TokenParsing m) => m Operator

operator = try infix' <|> postfix <|> try closed <|> prefix

-- | Parse a prefix operator.
--
-- >>> Trifecta.parseString operator mempty "if _ then _ else _"
-- Success (Prefix ("if" :| ["then","else"]))
prefix = Prefix <$> some1 (fragment <* placeholder)

-- | Parse a postfix operator.
--
-- >>> Trifecta.parseString operator mempty "_ [ _ ]"
-- Success (Postfix ("[" :| ["]"]))
postfix = Postfix <$> some1 (placeholder *> fragment)

-- | Parse an infix operator.
--
-- >>> Trifecta.parseString operator mempty "_ ⊢ _ : _"
-- Success (Infix ("\8866" :| [":"]))
infix' = Infix <$ placeholder <*> (fragment `endByNonEmpty` placeholder)

-- | Parse a closed operator.
--
-- >>> Trifecta.parseString operator mempty "| _ |"
-- Success (Closed "|" ("|" :| []))
closed = Closed <$> fragment <*> some1 (placeholder *> fragment)


-- | Parse a name fragment.
--
-- >>> foldResult (const Nothing) Just (Trifecta.parseString fragment mempty "_")
-- Nothing
fragment :: (Monad m, TokenParsing m) => m String
fragment = ident (IdentifierStyle "fragment" (letter <|> satisfy isOperator) (alphaNum <|> char '\'' <|> satisfy isOperator) mempty Identifier ReservedIdentifier)
  where isOperator '_' = False
        isOperator c   = isPunctuation c || isSymbol c
