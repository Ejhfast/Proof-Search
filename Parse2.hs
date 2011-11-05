module Parse2 where
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import ProofTypes
import List

neg a = Op "~" a (Var "NOP")
uncond_rule a = Op "#" (Var "NOP") a
sop_gen op a b = Op op a b
terminal ty a = 
  case ty of
    "rule" -> Free a
    _ -> Var a

make_rule_stmt :: Stmt String -> Rule String
make_rule_stmt stmt =
  case stmt of
    (Op "-->" a b) -> Rule a b Equality
    (Op "*->" a b) -> Rule a b Strict
    (Op "#" a b) -> Rule a b Unconditional
    _ -> Rule (Var "NOP") (Var "NOP") Strict -- fail...
    
make_rule :: String -> Rule String
make_rule str =
  let stmt = parse (expr "rule") "" str in
  case stmt of
    Right (Op "-->" a b) -> Rule a b Equality
    Right (Op "*->" a b) -> Rule a b Strict
    Right (Op "#" a b) -> Rule a b Unconditional
    _ -> Rule (Free "A") (Free "A") Strict -- fail...
    
make_ruleset :: String -> [String] -> String -> Ruleset String
make_ruleset name lst descr =
  let rules = List.map make_rule lst in
  Ruleset name rules descr

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
expr ty = do {x <- term ty; o <- binop; y <- term ty; return (Op o x y)}
  <|> do { char '('; x <- expr ty; char ')'; return x}
  <|> ground ty

term :: String -> Parser (Stmt String)
term ty = ground ty <|> expr ty
  
ground ty = do {x <- word; return (terminal ty x)}

binop :: Parser (String)
binop = string "+" <|> string "*" <|> string "=" <|> string "=>"
--unop = string "~"

word = many1 digit <|> many1 letter
