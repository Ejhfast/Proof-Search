module ProofParse where
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import ProofTypes
import Data.String.Utils
import Control.Monad
import List

-- Tex infastructure

parse_tex_command :: String -> Int -> Parser String -> Parser String
parse_tex_command command args parse_rest = do
	c <- string command
	m <- modifiers parse_rest
	get_args <- count args $ arg_parse parse_rest
	return c

arg_parse :: Parser String -> Parser String
arg_parse parse_rest = 
  do { char '{'; x <- parse_rest; char '}'; return x}

underscore :: Parser String -> Parser String
underscore parse_rest =
  do { string "_{"; x <- parse_rest; char '}'; return x}

carrot :: Parser String -> Parser String
carrot parse_rest =
  do { string "^{"; x <- parse_rest; char '}'; return x}
  
modifiers :: Parser String -> Parser String
modifiers parse_rest = do
  optional $ underscore parse_rest
  optional $ carrot parse_rest
  return "ok"

fake_parse :: Parser String
fake_parse = string "0"

tryall :: [Parser String] -> Parser String
tryall ps = foldr (\x -> (<|> (try x))) mzero ps

recurse :: Parser String
recurse = try fake_parse <|> all_funcs

all_funcs :: Parser String
all_funcs = tryall [x recurse | x <- [go,lala,eq_rw,rw]]

-- Basic Expressions
-- \eq_rewrite{A+B}{B+A}
-- \rewrite{A+B}{B+A}

-- expr = buildExpressionParser table primative <?> "expression"
-- primative = many1 digit
-- 
-- table = [
--     [prefix "~" neg]
--   , [op "." (sop_gen ".") AssocRight]
--   , [op "&" (sop_gen "&") AssocLeft, op "|" (sop_gen "|") AssocLeft, op "," (sop_gen ",") AssocLeft]
--   , [op "*" (sop_gen "*") AssocLeft, op "/" (sop_gen "/") AssocLeft]
--   , [op "+" (sop_gen "+") AssocLeft, op "-" (sop_gen "-") AssocLeft]
--   , op "=" (sop_gen "=") AssocLeft]
--   where
--     op s f assoc = Infix (do { string s; return f }) assoc
--     prefix name fun = Prefix (do{ string name; return fun })

-- Test

lala = parse_tex_command "\\lala" 3
go = parse_tex_command "\\go" 2
eq_rw = parse_tex_command "\\eq_rewrite" 2
rw = parse_tex_command "\\rewrite" 2


run_parse = do
	x <- all_funcs;
	eof;
	return x

  