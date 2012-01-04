module NewParse where
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import ProofTypes
import Data.String.Utils as Data
import Control.Monad
import List

-- Define Proof Data Types

data ProofLine = ProofLine {proof_name :: String, statement :: Stmt String, from_rules :: [String], with_assumps :: [String]}
  deriving (Eq,Show)

-- Helpers

remove_ws :: String -> String
remove_ws str =
  let sp_str = zip (split "\"" str) [0..] in
  Data.join "\"" [if (even i) then filter (\s -> s /= ' ' && s /= '\n') x else x | (x,i) <- sp_str]

-- Type helpers

-- Turn argument list into binary tree
argument_tree :: [Stmt String] -> Stmt String
argument_tree (x:xs) =
  case xs of
    [] -> Op "ARGS" x (Var "NOP")
    _ -> Op "ARGS" x (argument_tree xs)

func_tree :: String -> Stmt String -> Stmt String -> Stmt String    
func_tree op a b = Op op a b

unary_tree :: String -> Stmt String -> Stmt String
unary_tree op a = Op op a (Var "NOP")

make_rule :: Stmt String -> Rule String
make_rule stmt =
  case stmt of
    (Op "eq_rewrite" a b) -> Rule a b Equality
    (Op "rewrite" a b) -> Rule a b Strict
    _ -> Rule (Var "NOP") (Var "NOP") Strict -- fail...

make_rule_str str =
	let try = parse (recurse "free") "" str in
	case try of
		(Right x) -> make_rule x
		_ -> Rule (Var "NOP") (Var "NOP") Strict
		
make_stmt_str str =
	let try = parse (recurse "ground") "" str in
	case try of
		(Right x) ->  x
		_ -> Var "NOP"


    
do_parse_rule :: String -> Rule String
do_parse_rule str =
  let stmt = parse (run_parse "free") "" $ remove_ws str in
  case stmt of
    Right a -> make_rule a
    _ -> Rule (Free "A") (Free "A") Strict -- fail...
    

-- Tex infastructure

parse_tex_command :: String -> Int -> Parser (Stmt String) -> Parser (Stmt String)
parse_tex_command command args parse_rest = do
	c <- string $ "\\" ++ command
	m <- modifiers parse_rest
	get_args <- count args $ arg_parse parse_rest
	return $ Op command (argument_tree get_args) m

arg_parse :: Parser (Stmt String) -> Parser (Stmt String)
arg_parse parse_rest = 
  do { char '{'; x <- parse_rest; char '}'; return x}

underscore :: Parser (Stmt String) -> Parser (Stmt String)
underscore parse_rest =
  do { string "_{"; x <- parse_rest; char '}'; return x}

carrot :: Parser (Stmt String) -> Parser (Stmt String)
carrot parse_rest =
  do { string "^{"; x <- parse_rest; char '}'; return x}
  
modifiers :: Parser (Stmt String) -> Parser (Stmt String)
modifiers parse_rest = do
  u <- optionMaybe $ underscore parse_rest
  c <- optionMaybe $ carrot parse_rest
  case (u,c) of
    (Just uv, Just cv) -> return $ Op "Meta" uv cv
    (Just uv, Nothing) -> return $ Op "Meta" uv (Var "NOP")
    (Nothing, Just cv) -> return $ Op "Meta" (Var "NOP") cv
    _ -> return $ Op "Meta" (Var "NOP") (Var "NOP")

fake_parse :: Parser (Stmt String)
fake_parse = do { x <- string "0"; return (Var x) }

tryall :: [Parser (Stmt String)] -> Parser (Stmt String)
tryall ps = foldr (\x -> (<|> (try x))) mzero ps

-- Main calls here to parse out baby latex expressions

recurse :: String -> Parser (Stmt String)
recurse kind = try (expr (all_funcs kind) kind) <|> all_funcs kind

all_funcs :: String -> Parser (Stmt String)
all_funcs kind = tryall [x $ recurse kind | x <- [go,lala,cond,prob,norm,phi]]

-- Parse out rulesets

parse_rule :: Parser (Rule String)
parse_rule = do
  x <- recurse "free"; -- A rule is just a certain type of statement in the language
  return $ make_rule x

parse_ruleset :: Parser (Ruleset String)
parse_ruleset = do
  name <- get_symbol;
  string ":{\"";
  descrip <- get_description;
  string "\";";
  rules <- sepBy parse_rule (char ';');
  string "}";
  return $ Ruleset name rules descrip
  
parse_rulesets :: Parser [Ruleset String]
parse_rulesets = many1 parse_ruleset
  
parse_assumption :: Parser (Expr String)
parse_assumption = do
  name <- get_symbol;
  char ':';
  expr <- recurse "ground";
  char ';'
  return $ Expr name expr (Nothing,Nothing)

parse_assumptions :: Parser [Expr String]
parse_assumptions = many1 parse_assumption

parse_proofline :: Parser ProofLine
parse_proofline = do
  name <- get_symbol;
  char ':';
  conclusion <- recurse "ground";
  char ';';
  rules <- optionMaybe $ with_semi stringlist;
  assumptions <- optionMaybe $ with_semi stringlist;
  case (rules, assumptions) of
    (Just r, Just a) -> return $ ProofLine name conclusion r a
    (Just r, Nothing) -> return $ ProofLine name conclusion r []
    (Nothing, Just a) -> return $ ProofLine name conclusion [] a
    _ -> return $ ProofLine name conclusion [] []
    
parse_proof :: Parser [ProofLine]
parse_proof = many1 parse_proofline
  

-- Primative Expressions

with_semi p = do
  x <- p;
  char ';'
  return x;

stringlist :: Parser [String]
stringlist = do
  char '[';
  items <- sepBy get_symbol (char ',');
  char ']';
  return items

get_description :: Parser String
get_description = do
  ws <- sepBy get_symbol (string " ");
  return $ foldr (\x y -> x ++ " " ++ y) "" ws

get_symbol :: Parser String
get_symbol = many1 (digit <|> letter)

declared_constant :: Parser (Stmt String)
declared_constant = do {char '$'; x <- get_symbol; return (Var x)} <?> "constant"

number :: Parser (Stmt String)
number = do {x <- many1 digit; return (Var x)}

symbol :: String -> Parser (Stmt String)
symbol kind = do
  x <- get_symbol
  m <- modifiers $ recurse kind
  case m of
	Op "Meta" (Var "NOP") (Var "NOP") ->
		case kind of
			"free" -> return (Free x)
			"ground" -> return (Var x)
	_ ->
		case kind of
			"free" -> return $ Op "Symbol" (Free x) m
			"ground" -> return $ Op "Symbol" (Var x) m

factor :: Parser (Stmt String) -> String -> Parser (Stmt String)
factor tex_parse kind = do {char '('; x <- expr tex_parse kind; char ')'; return x }
  <|> declared_constant
  <|> number
  <|> symbol kind
  
expr tex_parse kind = buildExpressionParser table (new_p kind) <?> "expression"
  where new_p kind = tex_parse <|> (factor tex_parse kind)

table = [
    [prefix "~" (unary_tree "~")]
  , [op "." (func_tree ".") AssocRight]
  , [op "&" (func_tree "&") AssocLeft, op "|" (func_tree "|") AssocLeft, op "," (func_tree ",") AssocLeft]
  , [op "*" (func_tree "*") AssocLeft, op "/" (func_tree "/") AssocLeft]
  , [op "+" (func_tree "+") AssocLeft, op "-" (func_tree "-") AssocLeft]
  , [op "=" (func_tree "=") AssocLeft]
  , [op ":=" (func_tree "rewrite") AssocLeft, op "~>" (func_tree "eq_rewrite") AssocLeft] ]
  where
    op s f assoc = Infix (do { string s; return f }) assoc
    prefix name fun = Prefix (do{ string name; return fun })

-- Test

lala = parse_tex_command "lala" 3
go = parse_tex_command "go" 2
cond = parse_tex_command "cond" 2
prob = parse_tex_command "P" 1
norm = parse_tex_command "norm" 1
phi = parse_tex_command "t" 1
--eq_rw = parse_tex_command "eq_rewrite" 2
--rw = parse_tex_command "rewrite" 2

run_parse kind = do
	x <- recurse kind;
	eof;
	return x

ex_rule = "\\rewrite{\\go{1}{1}}{\\go{0}{0}+\\go{A_{1}^{2}}{0}}"
ex_ruleset = "myfule:{\"ok go\";"++ex_rule++";"++ex_rule++";"++ex_rule++"}"
test_parse = parse (run_parse "ground") "" ex_rule
test_ruleset = parse parse_ruleset "" $ ex_ruleset
test_rulesets = parse parse_rulesets "" $ ex_ruleset++ex_ruleset++ex_ruleset
test_rule = case test_parse of 
  Right x -> Just (make_rule x)
  _ -> Nothing

  