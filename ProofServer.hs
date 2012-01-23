module Main where
import Control.Monad (msum)
import Happstack.Server
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import List
import System.Timeout as S
import ProofParse
import ProofTypes as PT
import ProofSearch
import Text.JSON
import System.IO.Unsafe

main :: IO ()
main = simpleHTTP nullConf $ app

app :: ServerPart Response
app = do 
  decodeBody (defaultBodyPolicy "/tmp/" 0 10000 10000) 
  msum [   dir "check_proof" $ check_proof,
           dir "check_assignment" $ check_assign,
           dir "health" $ health ]

-- This is so S3 can test whether a server is responding           
health :: ServerPart Response
health = do
 methodM GET
 ok $ toResponse "Healthy"

check_proof :: ServerPart Response
check_proof = do
  methodM POST
  rulesets <- look "rulesets"
  frees <- look "frees"
  assumptions <- look "assumptions"
  conclusion <- look "conclusion"
  syntax <- look "syntax"
  let new_parse_funcs = if syntax == "" then [] else read syntax :: [(String, Int)]
  let rs_parsed = parse (parse_rulesets new_parse_funcs) "" $ remove_ws rulesets
  let as_parsed = parse (parse_assumptions new_parse_funcs) "" $ remove_ws assumptions
  let conc_parsed = parse (recurse "ground" new_parse_funcs) "" $ remove_ws conclusion
  case (rs_parsed, as_parsed, conc_parsed) of 
    (Right r, Right a, Right c) ->
      let wc = (Expr "_" c (Nothing,Nothing)) in
      case frees of
        "" -> do 
          res <- iter 3 r [] a [wc]
          ok $ toResponse res
        f  ->
          let fs_parsed = parse (parse_rulesets new_parse_funcs) "" $ remove_ws frees in
          case fs_parsed of
            (Right f) -> do
              res <- iter 3 r f a [wc]
              ok $ toResponse res
            f1 -> ok $ toResponse $ "Failure: bad parse in free rulesets."++(show f1)
    (p1,p2,p3) -> ok $ toResponse $ "Failure: bad parse in assumptions/rulesets."++(show p1)++(show p2)++(show p3)
    
check_assign :: ServerPart Response
check_assign = do
  methodM POST
  rulesets <- look "rulesets"
  assumptions <- look "assumptions"
  goal <- look "goal"
  syntax <- look "syntax"
  let new_parse_funcs = if syntax == "" then [] else read syntax :: [(String, Int)]
  let rs_parsed = parse (parse_rulesets new_parse_funcs) "" $ remove_ws rulesets
  let as_parsed = parse (parse_assumptions new_parse_funcs) "" $ remove_ws assumptions
  let g_parsed = parse (recurse "ground" new_parse_funcs) "" $ remove_ws goal
  case (rs_parsed, as_parsed, g_parsed) of 
    (Right r, Right a, Right go) -> ok $ toResponse $ "Success: Parsed assignment."
    (p1,p2,p3) -> ok $ toResponse $ "Failure: bad parse in assumptions/rulesets."++(show p1)++(show p2)++(show p3)
  

iter :: Int -> [Ruleset String] -> [Ruleset String] -> [Expr String] -> [Expr String] -> ServerPartT IO String
iter 0 _ _ _ _ = do { return $ "Failed to prove." }
iter depth rsets fsets assumps conc =
  let back = (++) conc $ back_apply_rulesets_stmts conc fsets in -- Look backward once with frees
  let expand_back = (++) back $ back_apply_rulesets_stmts back rsets in -- Generate one layer back from conclusion
  let fwrd = (++) assumps $ apply_rulesets_stmts assumps fsets in -- Look forward with frees
  let expand_fwrd = (++) fwrd $ apply_rulesets_stmts fwrd rsets in -- Generate one layer forward from assumptions
  let matches = [(x,y) | x <- expand_fwrd, y <- expand_back, (PT.body x) == (PT.body y)] in
  case matches of
    (x:rst) -> do { return "Proved" }
    _ -> iter (depth - 1) rsets fsets fwrd back
