module ProofParse where
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import ProofTypes
import Data.String.Utils
import List

forceList [] = ()
forceList (x:xs) = forceList xs

parse_tex_command :: String -> Int -> Parser String -> Parser String
parse_tex_command command args parse_rest = 
  case args of
    1 -> tex_1 command parse_rest
    2 -> tex_2 command parse_rest
    3 -> tex_3 command parse_rest
    4 -> tex_4 command parse_rest
    _ -> string "??fail??" <?> "fail" 
 
tex_1 :: String -> Parser String -> Parser String
tex_1 command parse_rest = do
  c <- string command
  m <- modifiers parse_rest
  a1 <- arg_parse parse_rest
  eof
  return c
  
tex_2 :: String -> Parser String -> Parser String
tex_2 command parse_rest = do
  c <- string command
  m <- modifiers parse_rest
  a1 <- arg_parse parse_rest
  a2 <- arg_parse parse_rest
  eof
  return c

tex_3 :: String -> Parser String -> Parser String
tex_3 command parse_rest = do
  c <- string command
  m <- modifiers parse_rest
  a1 <- arg_parse parse_rest
  a2 <- arg_parse parse_rest
  a3 <- arg_parse parse_rest
  eof
  return c

tex_4 :: String -> Parser String -> Parser String
tex_4 command parse_rest = do
  c <- string command
  m <- modifiers parse_rest
  a1 <- arg_parse parse_rest
  a2 <- arg_parse parse_rest
  a3 <- arg_parse parse_rest
  a4 <- arg_parse parse_rest
  eof
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

test_parse = parse_tex_command "/lala" 3 fake_parse
  