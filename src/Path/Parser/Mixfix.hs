module Path.Parser.Mixfix where

import Control.Applicative (Alternative(..), (<**>))
import Data.Char (isPunctuation, isSymbol)
import Data.HashSet (HashSet, fromList, member)
import Data.List.NonEmpty (some1)
import Path.Name
import Text.Parser.Token.Highlight
import Text.Trifecta as Trifecta

placeholder :: TokenParsing m => m ()
placeholder = () <$ token (char '_')


-- | Parse a mixfix operator.
--
-- >>> Trifecta.parseString (operator <* eof) mempty "_ ⊢ _ ∈ _"
-- Success (Infix ("\8866" :| ["\8712"]))
-- >>> Trifecta.parseString (operator <* eof) mempty "_ [ _ ]"
-- Success (Postfix ("[" :| ["]"]))
-- >>> Trifecta.parseString (operator <* eof) mempty "| _ |"
-- Success (Closed ("|" :| []) "|")
-- >>> Trifecta.parseString (operator <* eof) mempty "if _ then _ else _"
-- Success (Prefix ("if" :| ["then","else"]))
operator :: (Monad m, TokenParsing m) => m Operator
operator
  =   some1 (try (placeholder *> fragment)) <**> (Infix <$ placeholder <|> pure Postfix)
  <|> some1 (try (fragment <* placeholder)) <**> (flip Closed <$> fragment <|> pure Prefix)


-- | Parse a name fragment.
--
-- >>> foldResult (const Nothing) Just (Trifecta.parseString fragment mempty "_")
-- Nothing
fragment :: (Monad m, TokenParsing m) => m String
fragment = ident (IdentifierStyle "fragment" (letter <|> satisfy isOperator) (alphaNum <|> char '\'' <|> satisfy isOperator) reservedOperators Identifier ReservedIdentifier)
  where isOperator c
          | c `member` reservedOperatorChars = False
          | otherwise                        = isPunctuation c || isSymbol c

reservedOperators :: HashSet String
reservedOperators = fromList [ "->", ":" ]

reservedOperatorChars :: HashSet Char
reservedOperatorChars = fromList "(){}_"