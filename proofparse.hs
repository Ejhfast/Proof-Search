-- Parse strings into Expr and Rule types

module ProofParse where
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import ProofTypes
import List

neg a = Op "~" a (Var "NOP")
sop_gen op a b = Op op a b
terminal ty a = 
  case ty of
    "rule" -> Free a
    _ -> Var a

make_rule :: String -> Rule String
make_rule str =
  let stmt = parse (expr "rule") "" str in
  case stmt of
    Right (Op "-->" a b) -> Rule a b
    _ -> Rule (Free "A") (Free "A") -- fail...
    
make_ruleset :: String -> [String] -> Ruleset String
make_ruleset name lst =
  let rules = List.map make_rule lst in
  Ruleset name rules

make_stmt :: String -> Stmt String
make_stmt str =
  let stmt = parse (expr "stmt") "" str in
  case stmt of
    Right a -> a
    _ -> (Var "NOP") --fail
    
make_expr :: String -> String -> Expr String
make_expr name str =
  let stmt = make_stmt str in
  Expr name stmt (Nothing,Nothing)

expr :: String -> Parser (Stmt String)
expr ty = buildExpressionParser table (factor ty) <?> "expression"

table = [
    [prefix "~" neg]
  , [op "&" (sop_gen "&") AssocLeft, op "|" (sop_gen "|") AssocLeft, op "," (sop_gen ",") AssocLeft]
	, [op "=>" (sop_gen "=>") AssocLeft]
	, [op "-->" (sop_gen "-->") AssocLeft] ]
  where
    op s f assoc = Infix (do { string s; return f }) assoc
    prefix name fun = Prefix (do{ string name; return fun })

factor ty = do { char '('; x <- expr ty; char ')'; return x }
	 <|> number ty
	 <?> "simple expression"

word = many1 digit <|> many1 letter

number :: String -> Parser (Stmt String)
number ty = do { ds <- word; return (terminal ty ds) } <?> "number"