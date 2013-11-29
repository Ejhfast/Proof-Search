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
    _ -> Op "ARGS" x (argumentTree xs)

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

parseTexCommand command args parseRest = do
  c <- string $ "\\" ++ command
  m <- modifiers parseRest
  get_args <- count args $ argParse parseRest
  return $ Op command (argumentTree get_args) m
  
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
  [parseTexCommand name args | (name, args) <- lst]


argParse :: Parser (Stmt String) ->
             Parser (Stmt String)
argParse parseRest =
  do { 
    char '{'; 
    x <- parseRest; 
    char '}'; 
    return x
    }
--  char '{' parseRest char '}'


underscore :: Parser (Stmt String) ->
              Parser (Stmt String)
underscore parseRest =
  do { 
    string "_{"; 
    x <- parseRest; 
    char '}'; 
    return x
    }
--    string "_{" parseRest char '}'

carrot :: Parser (Stmt String) ->
          Parser (Stmt String)
carrot parseRest =
  do { 
    string "^{"; 
    x <- parseRest; 
    char '}'; 
    return x}
--  string "^{" parseRest char '}'

constraint :: Parser (Stmt String) ->
              Parser (Stmt String)
constraint parseRest =
  do { 
bound <- getSymbol; 
string "::"; x <- parseRest; 
return $ Op "CONSTRAINT" (Var bound) x 
}
  --do {    bound <- getSymbol string "::";    x <- parseRest;    return $ Op "CONSTRAINT" (Var bound) x    }

constraints :: Parser (Stmt String) ->
               Parser [Stmt String]
constraints parseRest =
  do {
    string "_[";
    constraint_list <- sepBy
                       (constraint parseRest)
                       (char ';');
    char ']';
    return constraint_list
    }

modifiers :: Parser (Stmt String) ->
             Parser (Stmt String)
modifiers parseRest = do
  u <- optionMaybe $ underscore parseRest
  c <- optionMaybe $ carrot parseRest
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
       allFuncs kind custom_tex)
    kind custom_tex) <|>
  allFuncs kind custom_tex

allFuncs :: String -> [(String, Int)] ->
             Parser (Stmt String)
allFuncs kind custom_tex =
  tryall [
    x $ recurse kind custom_tex |
    x <- createCommands custom_tex]


-- Parse out rulesets

parseRule :: [(String, Int)] ->
              Parser (Rule String)
parseRule custom_tex = do
  x <- recurse "free"
       custom_tex;
    -- A rule is just a certain type of statement in the language
  c <- optionMaybe $ constraints (recurse "ground" custom_tex);
  case c of
    Just cst -> return $ makeRule x cst
    _ -> return $ makeRule x []

parseRuleset :: [(String, Int)] ->
                 Parser (Ruleset String)
parseRuleset custom_tex = do
  name <- getSymbol;
  string "{";
  rules <- endBy (parseRule custom_tex) (char ';');
  optional $ char ';'
  string "}";
  return $ Ruleset name rules

parseRulesets :: [(String, Int)] -> Parser [Ruleset String]
parseRulesets custom_tex = many1 $ parseRuleset custom_tex

parseAssumption :: [(String, Int)] -> Parser (Expr String)
parseAssumption custom_tex = do
  name <- getSymbol;
  char ':';
  expr <- recurse "ground" custom_tex;
  char ';'
  return $ Expr name expr (
    Nothing , Nothing)

parseAssumptions :: [(String, Int)] -> Parser [Expr String]
parseAssumptions custom_tex = many1 $ parseAssumption custom_tex

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
  items <- sepBy getSymbol (char ',');
  char ']';
  return items

getSymbol :: Parser String
getSymbol = many1 (digit <|> letter)

declaredConstant :: Parser (Stmt String)
declaredConstant = do {
  char '$';
  x <- getSymbol;
  return (Var x);
  } <?> "constant"

number :: Parser (Stmt String)
number = do {
  x <- many1 digit;
  return (Var x);
  }


symbol :: String -> [(String , Int)] -> Parser (Stmt String)
symbol kind custom_tex = do
  x <- getSymbol
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
  do {char '('; x <- expr tex_parse kind custom_tex; char ')'; return x }
--  char '('
--  expr
--  tex_parse
--  kind
--  custom_tex char ')'
  <|> declaredConstant
  <|> number
  <|> symbol kind custom_tex

expr tex_parse kind custom_tex =
  buildExpressionParser table (
    new_p kind) <?> "expression"
  where new_p kind =
          tex_parse <|> factor tex_parse kind custom_tex

table = [
    [prefix "~" (unaryTree "~")]
  , [prefix "-" (unaryTree "-")]
  , [prefix "=" (unaryTree "__CNTS")]
  , [prefix "!" (unaryTree "__NOT_CNTS")]
  , [op "." (funcTree ".") AssocLeft]
  , [
       op "&" (funcTree "&")
       AssocLeft,
       op "|" (funcTree "|")
       AssocLeft,
       op "," (funcTree ",") AssocLeft
    ]
  , [op "*" (funcTree "*") AssocLeft, op "/" (funcTree "/") AssocLeft]
  , [op "+" (funcTree "+") AssocLeft, op "-" (funcTree "-") AssocLeft]
  , [
       op "=" (funcTree "=") AssocLeft,
       op "!=" (funcTree "!=") AssocLeft,
       op "<=" (funcTree "<=") AssocLeft,
       op ">=" (funcTree ">=") AssocLeft,
       op "<" (funcTree "<") AssocLeft,
       op ">" (funcTree ">") AssocLeft]
  , [
       op ":=" (funcTree "rewrite") AssocLeft,
       op "~>" (funcTree "eq_rewrite") AssocLeft] ]
  where
    op s f = Infix (do { string s; return f})
    prefix name fun = Prefix ( do { string name; return fun; }    )

runParse kind custom_tex = do
        x <- recurse kind custom_tex
        eof
        return x

