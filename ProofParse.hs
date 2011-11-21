module ProofParse where
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import ProofTypes
import Data.String.Utils
import List

-- unary generators
neg a = Op "~" a (Var "NOP")
sop_gen op a b = Op op a b
-- terminals
terminal ty a = 
  case ty of
    "rule" -> Free a
    _ -> Var a
-- some basic lexing
remove_ws str =
  let f_str = filter (\s -> s /= ' ') str in
  let sp_str = zip (split "\"" str) [0..] in
  join "\"" [if (even i) then replace "-->" ":r_eq" $ replace "=>" "?implies" x else x | (x,i) <- sp_str]
  

make_rule_stmt :: Stmt String -> Rule String
make_rule_stmt stmt =
  case stmt of
    (Op "-->" a b) -> Rule a b Equality
    (Op "*->" a b) -> Rule a b Strict
    _ -> Rule (Var "NOP") (Var "NOP") Strict -- fail...

--parse rule from string
make_rule :: String -> Rule String
make_rule str =
  let stmt = parse (expr "rule") "" $ remove_ws str in
  case stmt of
    Right (Op "-->" a b) -> Rule a b Equality
    Right (Op "*->" a b) -> Rule a b Strict
    _ -> Rule (Free "A") (Free "A") Strict -- fail...
    
make_ruleset :: String -> [String] -> String -> Ruleset String
make_ruleset name lst descr =
  let rules = List.map make_rule lst in
  Ruleset name rules descr

--parse stmt from string
make_stmt :: String -> Stmt String
make_stmt str =
  let stmt = parse (expr "stmt") "" $ remove_ws str in
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
  , [op "." (sop_gen ".") AssocRight]
  , [op "&" (sop_gen "&") AssocLeft, op "|" (sop_gen "|") AssocLeft, op "," (sop_gen ",") AssocLeft]
  , [op "*" (sop_gen "*") AssocLeft, op "/" (sop_gen "/") AssocLeft]
  , [op "+" (sop_gen "+") AssocLeft, op "-" (sop_gen "-") AssocLeft]
  , [op "?implies" (sop_gen "=>") AssocLeft, op "=" (sop_gen "=") AssocLeft]
	, [op ":r_eq" (sop_gen "-->") AssocLeft, op "~>" (sop_gen "*->") AssocLeft] ]
  where
    op s f assoc = Infix (do { string s; return f }) assoc
    prefix name fun = Prefix (do{ string name; return fun })

factor ty = do { ws; char '('; ws; x <- expr ty; ws; char ')'; ws; return x }
   <|> constant
	 <|> variable ty
	 <?> "statement"

word = many1 digit <|> many1 letter

variable :: String -> Parser (Stmt String)
variable ty = do { ds <- word; return (terminal ty ds) } <?> "variable"
constant :: Parser (Stmt String)
constant = do {char '$'; x <- word; return (terminal "stmt" x)} <?> "constant"

-- For web service

data ProofStmt = ProofStmt {nm :: String, stmt :: Stmt String, r_deps :: [String], a_deps :: [String]}
  deriving (Show,Eq)

r_expr = do {x <- (expr "rule"); ws; char ';'; ws; return x}
p_expr = do {x <- (expr "stmt"); ws; char ';'; ws; return x}

ruleset = do {ws; x <- digitstring; ws; char '{'; ws; d <- str; ws; y <- many r_expr; char '}'; ws; return (Ruleset x [make_rule_stmt r | r <- y] d)}
rulesets = many ruleset
assumption = do {w <- digitstring; char ':'; ws; x <- (expr "stmt"); char ';'; ws; return (Expr w x (Nothing,Nothing))}
assumptions = many assumption

proof_1l = do {line <- digitstring; char ':'; ws; x <- (expr "stmt"); ws; char ';'; ws; return (ProofStmt line x [] [])}
proof_2l = do {line <- digitstring; char ':'; ws; x <- p_expr; rules <- specifier; ws; char ';'; ws; return (ProofStmt line x rules [])}
proof_3l = do {line <- digitstring; char ':'; ws; x <- p_expr; rules <- specifier; ws; char ';'; ws; assumps <- specifier; ws; char ';'; ws; return (ProofStmt line x rules assumps)}

proof = try (many proof_3l) --(sepBy proof_3l eol)
  <|> try (many proof_2l) --(sepBy proof_2l eol)
  <|> many proof_1l --(sepBy proof_1l eol)

desc = digit <|> letter <|> char '-' <|> char '>' <|> char '<' <|> char '~' <|> char ' ' 
  <|> char '*' <|> char '+' <|> char '=' <|> char '(' <|> char ')' <|> char '.' <|> char '&' <|> char '|' <|> char ',' <|> char '⟘'
str = do {char '"'; x <- many desc; char '"'; return x }

specifier = do {char '['; x <- req; char ']'; return x}
req = sepBy digitstring (char ',') 
digitstring = many (digit <|> letter)
ws = many ((string " ") <|> eol)
eol =   try (string "\n\r")
    <|> try (string "\r\n")
    <|> string "\n"
    <|> string "\r"
    <?> "end of line"

