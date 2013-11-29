module ProofParse where
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import ProofTypes
import ProofFuncs
import Control.Monad
import Data.List

-- Define Proof Data Types

data ProofLine = ProofLine {
proofName :: String, statement :: Stmt String,
fromRules :: [String], withAssumps :: [String]
}
  deriving (Eq , Show)

-- Helpers

removeWs :: String -> String
removeWs = filter (\ s -> s /= ' ' && s /= '\n')

-- Type helpers

-- Turn argument list into binary tree
argumentTree :: [Stmt String] -> Stmt String
argumentTree [] = Op "ARGS" (Var "NOP") (Var "NOP")
argumentTree (x : xs) =
  case xs of
    [] -> Op "ARGS" x (Var "NOP")
    _ -> Op "ARGS" x (argument_tree xs)

funcTree :: String -> Stmt String -> Stmt String -> Stmt String
funcTree = Op

unaryTree :: String -> Stmt String -> Stmt String
unaryTree op a = Op op a (Var "NOP")

makeRule :: Stmt String -> [Stmt String] -> Rule String
makeRule stmt cons =
  case stmt of
    (Op "eq_rewrite" a b) -> Rule a b Equality cons
    (Op "rewrite" a b) -> Rule a b Strict cons
    _ -> Rule (Var "NOP") (Var "NOP") Strict []
-- fail... Tex infastructure

parseTexCommand :: String -> Int ->
     Parser (Stmt String) -> Parser (Stmt String)

parseTexCommand command args parse_rest = do
        c <- string $ '\\' ++ command
        m <- modifiers parse_rest
        get_args <- count args $ arg_parse parse_rest
        return $ Op command (argument_tree get_args) m

createCommands :: [
  (
    String,
    Int
  )
  ] ->
                  [
                    Parser (Stmt String) ->
                    Parser (Stmt String)
                  ]
createCommands lst =
  [parse_tex_command name args | (name, args) <- lst]


argParse :: Parser (Stmt String) ->
             Parser (Stmt String)
argParse parse_rest =
  char '{' parse_rest char '}'


underscore :: Parser (Stmt String) ->
              Parser (Stmt String)
underscore parse_rest =
    string "_{" parse_rest char '}'

carrot :: Parser (Stmt String) ->
          Parser (Stmt String)
carrot parse_rest =
  string "^{" parse_rest char '}'

constraint :: Parser (Stmt String) ->
              Parser (Stmt String)
constraint parse_rest =
  do {
    bound <- get_symbol string "::";
    x <- parse_rest;
    return $ Op "CONSTRAINT" (Var bound) x
    }

constraints :: Parser (Stmt String) ->
               Parser [Stmt String]
constraints parse_rest =
  do {
    string "_[";
    constraint_list <- sepBy
                       (constraint parse_rest)
                       (char ';');
    char ']';
    return constraint_list
    }

modifiers :: Parser (Stmt String) ->
             Parser (Stmt String)
modifiers parse_rest = do
  u <- optionMaybe $ underscore parse_rest
  c <- optionMaybe $ carrot parse_rest
  case (u , c) of
    (Just uv, Just cv) -> return $ Op "Meta" uv cv
    (Just uv, Nothing) -> return $ Op "Meta" uv (Var "NOP")
    (Nothing, Just cv) -> return $ Op "Meta" (Var "NOP") cv
    _ -> return $ Op "Meta" (Var "NOP") (Var "NOP")

fakeParse :: Parser (Stmt String)
fakeParse = do {
  x <- string "0";
  return (Var x)
  }

tryall :: [Parser (Stmt String)] ->
          Parser (Stmt String)
tryall = foldr (
  \ x ->
  (
    <|> try x
  )
  ) mzero

-- Main calls here to parse out baby latex expressions

recurse :: String -> [(String, Int)] ->
           Parser (Stmt String)
recurse kind custom_tex =
  try (
    expr (
       all_funcs kind custom_tex)
    kind custom_tex) <|>
  all_funcs kind custom_tex

allFuncs :: String -> [(String, Int)] ->
             Parser (Stmt String)
allFuncs kind custom_tex =
  tryall [
    x $ recurse kind custom_tex |
    x <- create_commands custom_tex]


-- Parse out rulesets

parseRule :: [(String, Int)] ->
              Parser (Rule String)
parseRule custom_tex = do
  x <- recurse "free"
       custom_tex;
    -- A rule is just a certain type of statement in the language
  c <- optionMaybe $ constraints (recurse "ground" custom_tex);
  case c of
    Just cst -> return $ make_rule x cst
    _ -> return $ make_rule x []

parseRuleset :: [(String, Int)] ->
                 Parser (Ruleset String)
parseRuleset custom_tex = do
  name <- get_symbol;
  string "{";
  rules <- endBy (parse_rule custom_tex) (char ';');
  optional $ char ';'
  string "}";
  return $ Ruleset name rules

parseRulesets :: [(String, Int)] -> Parser [Ruleset String]
parseRulesets custom_tex = many1 $ parse_ruleset custom_tex

parseAssumption :: [(String, Int)] -> Parser (Expr String)
parseAssumption custom_tex = do
  name <- get_symbol;
  char ':';
  expr <- recurse "ground" custom_tex;
  char ';'
  return $ Expr name expr (
    Nothing , Nothing)

parseAssumptions :: [(String, Int)] -> Parser [Expr String]
parseAssumptions custom_tex = many1 $ parse_assumption custom_tex

parseConclusion :: [(String, Int)] -> Parser [Expr String]
parseConclusion custom_tex = do
  conc <- recurse "ground" custom_tex;
  eof;
  return [
    Expr "_" conc (Nothing , Nothing)
    ]


-- Primative Expressions

withSemi p = do
  x <- p;
  char ';'
  return x;

stringlist :: Parser [String]
stringlist = do
  char '[';
  items <- sepBy get_symbol (char ',');
  char ']';
  return items

getSymbol :: Parser String
getSymbol = many1 (digit <|> letter)

declaredConstant :: Parser (Stmt String)
declaredConstant = do {
  char '$';
  x <- get_symbol;
  return (Var x);
  } <?> "constant"

number :: Parser (Stmt String)
number = do {
  x <- many1 digit;
  return (Var x);
  }


symbol :: String -> [(String , Int)] -> Parser (Stmt String)
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

factor :: Parser (Stmt String) ->
          String ->
          [(String , Int)] ->
          Parser ( Stmt String
  )
factor tex_parse kind custom_tex =
  char '(' expr tex_parse kind custom_tex char ')'
  <|> declared_constant
  <|> number
  <|> symbol kind custom_tex

expr tex_parse kind custom_tex =
  buildExpressionParser table (
    new_p kind) <?> "expression"
  where new_p kind =
          tex_parse <|> factor tex_parse kind custom_tex

table = [
    [prefix "~" (unary_tree "~")]
  , [prefix "-" (unary_tree "-")]
  , [prefix "=" (unary_tree "__CNTS")]
  , [prefix "!" (unary_tree "__NOT_CNTS")]
  , [op "." (func_tree ".") AssocLeft]
  , [
       op "&" (func_tree "&")
       AssocLeft,
       op "|" (func_tree "|")
       AssocLeft,
       op "," (func_tree ",") AssocLeft
    ]
  , [op "*" (func_tree "*") AssocLeft, op "/" (func_tree "/") AssocLeft]
  , [op "+" (func_tree "+") AssocLeft, op "-" (func_tree "-") AssocLeft]
  , [
       op "=" (func_tree "=") AssocLeft,
       op "!=" (func_tree "!=") AssocLeft,
       op "<=" (func_tree "<=") AssocLeft,
       op ">=" (func_tree ">=") AssocLeft,
       op "<" (func_tree "<") AssocLeft,
       op ">" (func_tree ">") AssocLeft]
  , [
       op ":=" (func_tree "rewrite") AssocLeft,
       op "~>" (func_tree "eq_rewrite") AssocLeft] ]
  where
    op s f = Infix (string s return f)
    prefix name fun = Prefix ( string name return fun   )

runParse kind custom_tex = do
        x <- recurse kind custom_tex
        eof
        return x

myTex = [
  ( "go", 2 ),
  ( "rewrite", 2 ) ,
  ("star" , 1) ,
  ("e" , 0)
  ]
