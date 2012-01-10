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
           dir "check_assignment" $ check_assign ]

check_proof :: ServerPart Response
check_proof = do 
  methodM POST
  rs <- look "rulesets"
  as <- look "assumptions"
  reqs <- look "reqs"
  p <- look "proof"
  goal <- look "goal"
  let rs_parsed = parse rulesets "" $ remove_ws rs
  let as_parsed = parse assumptions "" $ remove_ws as
  let g_parsed = parse (expr "stmt") "" $ remove_ws goal
  case (rs_parsed, as_parsed, g_parsed) of 
    (Right r, Right a, Right g) ->
      let pres = parse proof "" $ remove_ws p in
      case pres of
        Right pstmts -> do
          res <- do_proof r a pstmts g []
          ok $ toResponse res
        Left e -> ok $ toResponse (show e)
    _ -> ok $ toResponse "problem parsing"
    
check_assign :: ServerPart Response
check_assign = do
  methodM POST
  rs <- look "rulesets"
  as <- look "assumptions"
  g <- look "goal"
  let rs_parsed = parse rulesets "" $ remove_ws rs
  let as_parsed = parse assumptions "" $ remove_ws as
  let g_parsed = parse (expr "stmt") "" $ remove_ws g
  case (rs_parsed, as_parsed, g_parsed) of 
    (Right r, Right a, Right go) ->
      ok $ toResponse $ foldr (++) [] [pretty_ruleset x | x <- r]
    (p1,p2,p3) -> ok $ toResponse $ "Fail: bad parse in assumptions/rulesets\n"++(show p1)++"\n"++(show p2)++"\n"++(show p3)

proved :: [(String,(JSObject String))] -> ProofStmt -> [String] -> [String] -> [(String,(JSObject String))]
proved msg pstmt rules assums = ((nm pstmt),attrs):msg
  where attrs = toJSObject [("status","proved"),("rules",(show rules)),("assumptions",(show assums))]
  --msg++"Proved "++(nm pstmt)++" with "++(show rules)++" and assumptions "++(show assums)++".\n"
failed :: [(String,(JSObject String))] -> ProofStmt -> [Expr String] -> [(String,(JSObject String))]
failed msg pstmt [] = ((nm pstmt),attrs):msg
  where attrs = toJSObject [("status","failed")]
failed msg pstmt (h:hs) = ((nm pstmt),attrs):msg
  where attrs = toJSObject [("status","failed"),("hint_rules",(show $ rule_deps h)),("hint_assumps",(show $ deps h))]
  
  --msg++"Failed to prove "++(nm pstmt)++" with "++(show $ r_deps pstmt)++" and assumptions "++(show $ a_deps pstmt)++".\n"
  
pretty_ruleset :: Ruleset String -> String
pretty_ruleset ruleset =
  (show $ name ruleset)++": "++(show $ descrip ruleset)++"\n" 

do_proof :: [Ruleset String] -> [Expr String] -> [ProofStmt] -> Stmt String -> [(String,(JSObject String))] -> ServerPartT IO String
do_proof _ _ [] _ msg = do { return $ encode $ toJSObject msg }
do_proof rs as (p:ps) goal msg = do
  let use_rules = if (r_deps p) == [] then rs else filter (\r -> ((name r) `elem` (r_deps p)) || (name r) == "Free" ) rs
  let use_assumps = if (a_deps p) == [] then as else filter (\a -> (_id a) `elem` (a_deps p)) as
  try_prove <- checkproof 3 (stmt p) use_rules use_assumps
  case try_prove of
    Just (x:xs) ->
      case verify_rules_assumptions (x:xs) (r_deps p) (a_deps p) of
        True -> let newassum = Expr (nm p) (stmt p) (Nothing,Nothing) in
          if (PT.body x) == goal then return $ encode $ toJSObject $ (proved msg p (rule_deps x) (deps x))
            else do_proof rs (newassum:as) ps goal (proved msg p (rule_deps x) (deps x))
        False -> return $ encode $ toJSObject $ failed msg p []
    _ -> do
      try_prove <- checkproof 5 (stmt p) rs as
      case try_prove of
        Just x -> return $ encode $ toJSObject $ failed msg p x
        otherwise -> return $ encode $ toJSObject $ failed msg p []

verify_rules_assumptions :: [Expr String] -> [String] -> [String] -> Bool
verify_rules_assumptions exprs [] [] = True
verify_rules_assumptions exprs r_d [] = match_d rule_deps exprs r_d
verify_rules_assumptions exprs [] a_d = match_d deps exprs a_d
verify_rules_assumptions exprs r_d a_d = (match_d deps exprs a_d) && (match_d rule_deps exprs r_d)

match_d :: (Expr String -> [String]) -> [Expr String] -> [String] -> Bool
match_d f [] m = False
match_d f (x:xs) m = 
  let rules = sort $ filter (\x -> x /= "Free" && x /= "_") (f x) in
  let ms = filter (\f-> f /= "" && f /= "Free") $ sort m in
  if ms == rules then True else match_d f xs m

f_search :: Int -> Stmt String -> [Expr String] -> [Ruleset String] -> [Expr String] -> IO (Maybe [Expr String])
f_search 0 _ _ _ stmts = do {return $ Nothing }
f_search depth start toprove rulesets stmts = 
  let update = stmts ++ apply_rulesets_stmts stmts rulesets in
  let res = [Expr "_" start (Just ((rule_deps x)++(rule_deps y)), Just (merge_deps (deps x) (deps y))) | (x,y) <- (contains toprove update)] in
  case res of 
    (x:rst) -> do {return $ Just res}
    _ -> f_search (depth - 1) start toprove rulesets update
    
timed_search :: Int -> Stmt String -> [Expr String] -> [Ruleset String] -> [Expr String] -> (Maybe [Expr String])
timed_search depth start toprove rulesets stmts = 
  let search = unsafePerformIO $ S.timeout 1000000 $ f_search depth start toprove rulesets stmts in
  case search of
    Just x -> x
    Nothing -> Nothing

checkproof :: Int -> Stmt String -> [Ruleset String] -> [Expr String] -> ServerPartT IO (Maybe [Expr String])
checkproof depth stmt rulesets assumps =
  let equiv = backward_search 1 (Expr "_" stmt (Nothing,Nothing)) assumps rulesets in -- find things equivalent to the goal
  do { return $ timed_search depth stmt equiv rulesets assumps }