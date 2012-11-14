module ProofTest where
import Data.List  
import ProofSearch
import ProofParse
import ProofTypes
import ProofFuncs
import System.Timeout
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr

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

iter :: Int -> [Ruleset String] -> [Ruleset String] -> [Expr String] -> [Expr String] -> IO (Maybe String)
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
    
verify :: Int -> [Expr String] -> [Ruleset String] -> [Expr String] -> IO (Maybe String)
--verify :: Int -> [Expr String] -> [Ruleset String] -> [Expr String] -> IO String
verify depth stmt rulesets assumps =
  iter depth rulesets [] assumps stmt
--  let equiv = backward_search 1 (Expr "_" stmt (Nothing,Nothing)) assumps rulesets in -- find things equivalent to the goal
--  do {return $ forward_search depth stmt equiv rulesets assumps }

run_test to_prove rulesets stmts = do
  res <- verify 4 to_prove rulesets stmts
  case res of
    (Just x) -> return x
    Nothing -> return "failed"
  
time_test to_prove rulesets stmts = do
  res <- timeout 1000000 (run_test to_prove rulesets stmts) -- .1 second to return answer
  case res of
    (Just x) -> return x
    Nothing -> return "failed"

make_rulesets rulesets =
  parse (parse_rulesets []) "" rulesets

make_assumptions assumps =
  parse (parse_assumptions []) "" assumps

make_conc conc = do
  res <- parse (parse_conclusion []) "" conc
  case res of
    (Just res) -> return res

test1 =
  let r1 = "Neg{~(~A):=A;(A,B)~>A&B;}" in
  let r2 = "TP{A,(A=>B)~>B;}" in
  let s1 = "A1:~(~Z)=>F;" in
  let s2 = "A2:F=>D;" in
  let s3 = "A3:Z;" in
  let to_prove = "Z&(Z=>F)" in
  time_test (make_conc to_prove) (make_rulesets r1++r2) (make_assumptions s1++s2++s3)

  
  {-
test2 =
  let r2 = make_ruleset "DL" ["~(A&B)-->~A|~B","~(A|B)-->~A&~B"] ""  in
  let r3 = make_ruleset "TP" ["A,(A=>B)~>B","(A=>B),(B=>C)~>(A=>C)"] ""  in
  let s1 = make_expr "A1" "~(A&B)=>C" in
  let s2 = make_expr "A2" "C=>D" in
  let to_prove = make_stmt "~A|~B=>C" in
  time_test to_prove [r2,r3] [s1,s2]
  
test3 = 
  let r1 = make_ruleset "Free" ["(A,B)~>A&B"] ""  in
  let s1 = make_expr "A1" "A" in
  let s2 = make_expr "A2" "B" in
  let s3 = make_expr "A3" "C" in
  let s4 = make_expr "A4" "D" in
  let s5 = make_expr "A5" "E" in
  let to_prove = make_stmt "A&B&C" in
  time_test to_prove [r1] [s1,s2,s3,s4,s5]
  
test4 =
  let r2 = make_ruleset "DL" ["~(A&B)-->~A|~B","~(A|B)-->~A&~B"] ""  in
  let s1 = make_expr "A1" "A&~(B|C)=>C" in
  let to_prove = make_stmt "A&(~B&~C)=>C" in
  time_test to_prove [r2] [s1]
  
test5 =
  let fr = make_ruleset "Free" ["~(~A)-->A","(Q=>A&C)-->(Q=>A)","A&B-->B&A"] ""  in
  let tp = make_ruleset "TP" ["A,(A=>B)-->B"] ""  in
  let dl = make_ruleset "DL" ["~(A&B)-->~A|~B","~(A|B)-->~A&~B"] "" in
  let s1 = make_expr "A1" "~K=>~(Q|M)" in
  let to_prove = make_stmt "~K=>~Q" in
  time_test to_prove [dl,fr,tp] [s1]
  
test6 =
  let r1 = make_ruleset "Free" ["~(~A)-->A","A-->~(~A)"] ""  in
  let r2 = make_ruleset "DL" ["~(A&B)-->~A|~B","~(A|B)-->~A&~B"] ""  in
  let s1 = make_expr "A1" "~(A&(B|C))=>C" in
  let to_prove = make_stmt "~A|(~B&~C)=>C" in
  time_test to_prove [r1,r2] [s1]

test7 =
  let r1 = make_ruleset "Free" ["A,B-->B&A"] ""  in
  let r2 = make_ruleset "TP" ["A,(A=>B)-->B"] ""  in
  let s1 = make_expr "A1" "A=>B" in
  let s2 = make_expr "A2" "B=>C" in
  let s3 = make_expr "A3" "C=>D" in
  let s4 = make_expr "A4" "A" in
  let to_prove = make_stmt "B&A" in
  time_test to_prove [r1,r2] [s1,s2,s3,s4]

test8 = 
	let r1 = make_ruleset "Dist" ["A*X+B*X-->(A+B)*X"] ""  in
	let s1 = make_expr "A1" "2*X+3*X+(3*Y+4*Y)" in
	let to_prove = make_stmt "5*X+7*Y" in
	time_test to_prove [r1] [s1]
  
test9 = 
	let r1 = make_ruleset "Math" ["A*X+B*X-->(A+B)*X"] ""  in
	let s1 = make_expr "A1" "2*X+3*X+(5*4)" in
	let to_prove = make_stmt "5*X+20" in
	time_test to_prove [r1] [s1]

test10 =
  let r1 = make_ruleset "Math" ["A*X+B*X-->(A+B)*X"] ""  in
  let s1 = make_expr "A1" "(1*Y)*X+(2*Y)*X" in
  let to_prove = make_stmt "(1*Y+2*Y)*X" in
  time_test to_prove [r1] [s1]

test11 = 
  let r1 = make_ruleset "Ex" ["$B-->$a.$B.$a","$B-->$nil","$B-->$B.$B"] ""  in
  let s1 = make_expr "A1" "B" in
  let to_prove = make_stmt "a.B.a.B.a.a" in
  time_test to_prove [r1] [s1]

test12 =
  let r1 = make_ruleset "Free" ["A~>A|B","A=>B-->~B=>~A"] ""  in
  let s1 = make_expr "A1" "A=>B" in
  let to_prove = make_stmt "(~B=>~A)|C" in
  time_test to_prove [r1] [s1]
  
test13 =
  let r1 = make_ruleset "Imp" ["(A=>A)"] ""  in
  let s1 = make_expr "A1" "B" in
  let to_prove = make_stmt "(V=>V)=>(V=>V)" in
  time_test to_prove [r1] [s1]
  
test14 =
  let r1 = make_ruleset "Uni" ["#(A&B)","#(A&B&C)"] ""  in
  let s1 = make_expr "A1" "Q" in
  let s2 = make_expr "A2" "R" in
  let to_prove = make_stmt "Q&R" in
  time_test to_prove [r1] [s1,s2]
  
test15 = 
  let r1 = make_ruleset "T" ["A,(A&B=>C)-->B=>C","#(A,B)"] "" in
  let s1 = make_expr "A1" "~R&~B=>~K" in
  let s2 = make_expr "A2" "~R" in
  let to_prove = make_stmt "~B=>~K" in
  time_test to_prove [r1] [s1,s2]

test16 = 
  let r1 = make_ruleset "T" ["(P=>Q),(Q=>R)~>(P=>R)","#(A,B)"] "" in
  let s1 = make_expr "A1" "~A=>(D&F&G)" in
  let s2 = make_expr "A2" "(D&F&G)=>~B" in
  let to_prove = make_stmt "~A=>~B" in
  time_test to_prove [r1] [s1,s2] 
  
-- bad tests, mostly testing "general rewrites vs. equality"

bad1 = 
  let r1 = make_ruleset "Free" ["A~>A|B","A&B~>A"] ""  in
  let s1 = make_expr "A1" "A&B=>C" in
  let to_prove = make_stmt "A=>C" in
  time_test to_prove [r1] [s1]
  
bad2 = 
  let r1 = make_ruleset "Free" ["A~>A|B","A&B~>A","A~>A&B"] ""  in
  let s1 = make_expr "A1" "A=>C" in
  let s2 = make_expr "A2" "B" in
  let to_prove = make_stmt "A|B=>C" in
  time_test to_prove [r1] [s1,s2]

bad3 =
  let r1 = make_ruleset "B" ["B-->C+C"] ""  in
  let s1 = make_expr "A1" "A" in
  let s2 = make_expr "A2" "B" in
  let to_prove = make_stmt "B+A" in
  time_test to_prove [r1] [s1,s2]


run_good = mapM (\f -> (f)) [test1,test2,test3,test4,test5,test6,test7,test8,test9,test10,test11,test12,test13,test14]
run_bad = mapM (\f -> (f)) [bad1,bad2,bad3]-}
