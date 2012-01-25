module ProofParse where
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

make_rule :: Stmt String -> Rule String
make_rule stmt =
  case stmt of
    (Op "eq_rewrite" a b) -> Rule a b Equality
    (Op "rewrite" a b) -> Rule a b Strict
    _ -> Rule (Var "NOP") (Var "NOP") Strict -- fail...

make_rule_str str custom_tex =
	let try = parse (recurse "free" custom_tex) "" str in
	case try of
		(Right x) -> make_rule x
		_ -> Rule (Var "NOP") (Var "NOP") Strict
		
make_stmt_str str custom_tex =
	let try = parse (recurse "ground" custom_tex) "" str in
	case try of
		(Right x) ->  x
		_ -> Var "NOP"


    
do_parse_rule :: String -> [(String, Int)] -> Rule String
do_parse_rule str custom_tex =
  let stmt = parse (run_parse "free" custom_tex) "" $ remove_ws str in
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
  return $ make_rule x

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
  , [op ":=" (func_tree "rewrite") AssocLeft, op "~>" (func_tree "eq_rewrite") AssocLeft] ]
  where
    op s f assoc = Infix (do { string s; return f }) assoc
    prefix name fun = Prefix (do{ string name; return fun })

run_parse kind custom_tex = do
	x <- recurse kind custom_tex;
	eof;
	return x
	
mytex = [("go",2),("rewrite",2)]

ex_rule = "\\rewrite{\\go{1}{1}}{\\go{0}{0}+\\go{A_{1}^{2}}{0}}"
ex_ruleset = "myfule{"++ex_rule++";"++ex_rule++";"++ex_rule++"}"
ex_ruleset2 = "Test{X+Y~>Y+X;X+Y:=Y+X;}"
test_parse = parse (run_parse "ground" mytex) "" ex_rule
test_ruleset = parse (parse_ruleset mytex) "" $ ex_ruleset2
test_rulesets = parse (parse_rulesets mytex) "" $ ex_ruleset++ex_ruleset++ex_ruleset
test_rule = case test_parse of 
  Right x -> Just (make_rule x)
  _ -> Nothing

  