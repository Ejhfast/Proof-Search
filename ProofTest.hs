module Main where
import Control.Monad
import Control.Monad (msum)
import Control.Monad.Instances
import Data.Char
import Data.List  
import Data.Maybe
import Debug.Trace
import ProofFuncs
import ProofParse
import ProofSearch
import ProofTypes
import System.Environment
import System.IO.Unsafe
import System.Timeout as S
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Expr
import Text.Printf
import Text.Show


{-
iter :: Int -> [Ruleset String] -> [Ruleset String] -> [Expr String] -> [Expr String] -> IO String
iter 0 _ _ _ _ = do { return $ "Failed to prove." }
iter depth rsets fsets assumps conc =
  let back = (++) conc $ back_apply_rulesets_stmts conc fsets in -- Look backward once with frees
  let expand_back = (++) back $ back_apply_rulesets_stmts back rsets in -- Generate one layer back from conclusion
  let fwrd = (++) assumps $ apply_rulesets_stmts assumps fsets in -- Look forward with frees
  let expand_fwrd = (++) fwrd $ apply_rulesets_stmts fwrd rsets in -- Generate one layer forward from assumptions
  let matches = [(x,y) | x <- expand_fwrd, y <- expand_back, (ProofTypes.body x) == (ProofTypes.body y)] in
  case matches of
    (x:rst) -> do { return "Proved" }
    _ -> iter (depth - 1) rsets fsets fwrd back
-}

iter :: Int -> [Ruleset String] -> [Ruleset String] -> [Expr String] -> [Expr String] -> IO ([Char])
iter 0 _ _ _ _ = do { return $ "Failed to prove." }
iter depth rsets fsets assumps conc =
  let back = (++) conc $ back_apply_rulesets_stmts conc fsets in -- Look backward once with frees
  let expand_back = (++) back $ back_apply_rulesets_stmts back rsets in -- Generate one layer back from conclusion
  let fwrd = (++) assumps $ apply_rulesets_stmts assumps fsets in -- Look forward with frees
  let expand_fwrd = (++) fwrd $ apply_rulesets_stmts fwrd rsets in -- Generate one layer forward from assumptions
  let matches = [(x,y) | x <- expand_fwrd, y <- expand_back, (ProofTypes.body x) == (ProofTypes.body y)] in
  case matches of
    (x:rst) -> do { return "Proved" }
    _ -> iter (depth - 1) rsets fsets fwrd back


{-forward_search :: Int -> Stmt String -> [Expr String] -> [Ruleset String] -> [Expr String] -> Maybe String
forward_search 0 _ _ _ stmts = Nothing
forward_search depth start toprove rulesets stmts = 
  let update = stmts ++ apply_rulesets_stmts stmts rulesets in
  let res = [Expr "_" start (Just ((rule_deps x)++(rule_deps y)), Just (merge_deps (deps x) (deps y))) | (x,y) <- (contains toprove update)] in
  case res of 
    (x:rst) -> Just (show_expr x)
    _ -> forward_search (depth - 1) start toprove rulesets $ nub update
-}
    
verify :: Int -> [Expr String] -> [Ruleset String] -> [Expr String] -> IO ([Char])
--verify :: Int -> [Expr String] -> [Ruleset String] -> [Expr String] -> IO String
verify depth stmt rulesets assumps =
  iter depth rulesets [] assumps stmt
--  let equiv = backward_search 1 (Expr "_" stmt (Nothing,Nothing)) assumps rulesets in -- find things equivalent to the goal
--  do {return $ forward_search depth stmt equiv rulesets assumps }

run_test to_prove rulesets stmts = do
  --res <- verify 4 to_prove rulesets stmts
  return verify 4 to_prove rulesets stmts
--  case res of
   -- (Just x) -> return x
--    Nothing -> return "failed"
  
--time_test to_prove rulesets stmts = do
--  res <- timeout 1000000 (run_test to_prove rulesets stmts) -- .1 second to return answer
--  case res of
--    (Just x) -> return x
--    Nothing -> return "failed"

make_ruleset ruleset =
  parse (parse_rulesets []) "" ruleset

make_rulesets rulesets =
  parse (parse_rulesets []) "" rulesets

make_assumptions assumps =
  parse (parse_assumptions []) "" assumps

--make_conc conc = do
--  res <- parse (parse_conclusion []) "" conc
--  case res of
--   (Just res) -> return res

make_conc conc2 = do
--  res <-  
  parse (parse_conclusion []) "" conc2
--  case res of
--    (ParseError ) -> return res
    --( [Expr String] res) -> return res
--    (Just res) -> return res

--  res <- parse (parse_conclusion []) "" conc
--  case res of
--   (Just res) -> return res


-- Test for empty string as input, otherwise parse
maybe_parse :: (Parser [a]) -> String -> Maybe [a]
maybe_parse parser str =
  if str == "" then Just [] else
    let tryit = parse parser "" str in
    case tryit of
      (Right res) -> Just res
      _ -> Nothing

main :: IO ()
main = io (map processIt)
io f = interact (unlines . f . lines)

processIt s = do 
--  show( parse (parse_rulesets []) "" s)
  show( parse (parse_assumptions []) "" s)
--  show( parse (parse_conclusion []) "" s)
