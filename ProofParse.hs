module ProofParse where
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import ProofTypes
import ProofFuncs
import Data.String.Utils as Data
import Control.Monad
import List

-- Define Proof Data Types

data ProofLine = ProofLine {proof_name :: String, statement :: Stmt String, from_rules :: [String], with_assumps :: [String]}
  deriving (Eq,Show)

-- Helpers

remove_ws :: String -> String
remove_ws = filter (\s -> s /= ' ' && s /= '\n')

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

make_rule :: Stmt String -> [Stmt String] -> Rule String
make_rule stmt cons =
  case stmt of
    (Op "eq_rewrite" a b) -> Rule a b Equality cons
    (Op "rewrite" a b) -> Rule a b Strict cons
    _ -> Rule (Var "NOP") (Var "NOP") Strict [] -- fail...
    
-- Tex infastructure

parse_tex_command :: String -> Int -> Parser (Stmt String) -> Parser (Stmt String)
parse_tex_command command args parse_rest = do
	c <- string $ "\\" ++ command
	m <- modifiers parse_rest
	get_args <- count args $ arg_parse parse_rest
	return $ Op command (argument_tree get_args) m
	
create_commands :: [(String, Int)] -> [(Parser (Stmt String) -> Parser (Stmt String))]
create_commands lst = 
  [parse_tex_command name args | (name, args) <- lst]

arg_parse :: Parser (Stmt String) -> Parser (Stmt String)
arg_parse parse_rest = 
  do { char '{'; x <- parse_rest; char '}'; return x}

underscore :: Parser (Stmt String) -> Parser (Stmt String)
underscore parse_rest =
  do { string "_{"; x <- parse_rest; char '}'; return x}

carrot :: Parser (Stmt String) -> Parser (Stmt String)
carrot parse_rest =
  do { string "^{"; x <- parse_rest; char '}'; return x}

constraint :: Parser (Stmt String) -> Parser (Stmt String)
constraint parse_rest = 
  do { bound <- get_symbol; string "::"; x <- parse_rest; return $ Op "CONSTRAINT" (Var bound) x }

constraints :: Parser (Stmt String) -> Parser ([Stmt String])
constraints parse_rest =
  do { string "_["; constraint_list <- sepBy (constraint parse_rest) (char ';'); char ']'; return $ constraint_list }
  
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

recurse :: String -> [(String, Int)] -> Parser (Stmt String)
recurse kind custom_tex = try (expr (all_funcs kind custom_tex) kind custom_tex) <|> all_funcs kind custom_tex

all_funcs :: String -> [(String, Int)] -> Parser (Stmt String)
all_funcs kind custom_tex = tryall [x $ recurse kind custom_tex | x <- create_commands custom_tex]--[go,lala,cond,prob,norm,phi]]

-- Parse out rulesets

parse_rule :: [(String, Int)] -> Parser (Rule String)
parse_rule custom_tex = do
  x <- recurse "free" custom_tex; -- A rule is just a certain type of statement in the language
  c <- optionMaybe $ constraints (recurse "ground" custom_tex);
  case c of
    Just cst -> return $ make_rule x cst
    _ -> return $ make_rule x []

parse_ruleset :: [(String, Int)] -> Parser (Ruleset String)
parse_ruleset custom_tex = do
  name <- get_symbol;
  string "{";
  rules <- endBy (parse_rule custom_tex) (char ';');
  optional $ char ';'
  string "}";
  return $ Ruleset name rules
  
parse_rulesets :: [(String, Int)] -> Parser [Ruleset String]
parse_rulesets custom_tex = many1 $ parse_ruleset custom_tex
  
parse_assumption :: [(String, Int)] -> Parser (Expr String)
parse_assumption custom_tex = do
  name <- get_symbol;
  char ':';
  expr <- recurse "ground" custom_tex;
  char ';'
  return $ Expr name expr (Nothing,Nothing)

parse_assumptions :: [(String, Int)] -> Parser [Expr String]
parse_assumptions custom_tex = many1 $ parse_assumption custom_tex

parse_conclusion :: [(String, Int)] -> Parser [(Expr String)]
parse_conclusion custom_tex = do
  conc <- recurse "ground" custom_tex;
  eof;
  return $ [Expr "_" conc (Nothing,Nothing)]
  

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

get_symbol :: Parser String
get_symbol = many1 (digit <|> letter)

declared_constant :: Parser (Stmt String)
declared_constant = do {char '$'; x <- get_symbol; return (Var x)} <?> "constant"

number :: Parser (Stmt String)
number = do {x <- many1 digit; return (Var x)}

symbol :: String -> [(String,Int)] -> Parser (Stmt String)
symbol kind custom_tex = do
  x <- get_symbol
  m <- modifiers $ recurse kind custom_tex
  case m of
	Op "Meta" (Var "NOP") (Var "NOP") ->
		case kind of
			"free" -> return (Free x)
			"ground" -> return (Var x)
	_ ->
		case kind of
			"free" -> return $ Op "Symbol" (Free x) m
			"ground" -> return $ Op "Symbol" (Var x) m

factor :: Parser (Stmt String) -> String -> [(String,Int)] -> Parser (Stmt String)
factor tex_parse kind custom_tex = do {char '('; x <- expr tex_parse kind custom_tex; char ')'; return x }
  <|> declared_constant
  <|> number
  <|> symbol kind custom_tex
  
expr tex_parse kind custom_tex = buildExpressionParser table (new_p kind) <?> "expression"
  where new_p kind = tex_parse <|> (factor tex_parse kind custom_tex)

table = [
    [prefix "~" (unary_tree "~")]
  , [prefix "-" (unary_tree "-")]
  , [op "." (func_tree ".") AssocRight]
  , [op "&" (func_tree "&") AssocLeft, op "|" (func_tree "|") AssocLeft, op "," (func_tree ",") AssocLeft]
  , [op "*" (func_tree "*") AssocLeft, op "/" (func_tree "/") AssocLeft]
  , [op "+" (func_tree "+") AssocLeft, op "-" (func_tree "-") AssocLeft]
  , [op "=" (func_tree "=") AssocLeft]
  , [op "!=" (func_tree "!=") AssocLeft]
  , [op ":=" (func_tree "rewrite") AssocLeft, op "~>" (func_tree "eq_rewrite") AssocLeft] ]
  where
    op s f assoc = Infix (do { string s; return f }) assoc
    prefix name fun = Prefix (do{ string name; return fun })

run_parse kind custom_tex = do
	x <- recurse kind custom_tex;
	eof;
	return x
	
mytex = [("go",2),("rewrite",2)]

ex_rule = "\\rewrite{X}{\\go{0}{0}+\\go{A_{1}^{2}}{0}}_[X::(X=2);Y::(Y!=2)]"
ex_ruleset = "myfule{"++ex_rule++";"++ex_rule++";"++ex_rule++"}"
ex_ruleset2 = "Test{X+Y~>Y+X;X+Y:=Y+X;}"
test_parse = parse (parse_rule mytex) "" ex_rule
test_ruleset = parse (parse_ruleset mytex) "" $ ex_ruleset2
test_rulesets = parse (parse_rulesets mytex) "" $ ex_ruleset++ex_ruleset++ex_ruleset
cond_ruleset = "TestRule{(X+Y+Z~>Z+X+Y)_[Z::(Z=1)];}"

  