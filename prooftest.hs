module ProofTest where
import List  
import ProofSearch
import ProofParse
import ProofTypes

test1 =
  let r1 = make_ruleset "Free" ["~(~A)-->A","A,A-->A","A,B-->B,A"] in
  let r2 = make_ruleset "TP" ["A,(A=>B)-->B"] in
  let s1 = make_expr "A1" "~(~Z)=>F" in
  let s2 = make_expr "A2" "F=>D" in
  let s3 = make_expr "A3" "Z" in
  let to_prove = make_stmt "D" in
  check_proof 4 to_prove [r1,r2] [s1,s2,s3] 
  
test2 =
  let r1 = make_ruleset "Free" ["A,A-->A","A,B-->B,A"] in
  let r2 = make_ruleset "DL" ["~(A&B)-->~A|~B","~(A|B)-->~A&~B"] in
  let r3 = make_ruleset "TP" ["A,(A=>B)-->B","(A=>B),(B=>C)-->(A=>C)"] in
  let s1 = make_expr "A1" "~(A&B)=>C" in
  let s2 = make_expr "A2" "C=>D" in
  let to_prove = make_stmt "~A|~B=>D" in
  check_proof 4 to_prove [r1,r2,r3] [s1,s2]
  
test3 = 
  let r1 = make_ruleset "Free" ["~(~A)-->A","A,A-->A","A,B-->B,A","A,B-->A&B"] in
  let s1 = make_expr "A1" "A" in
  let s2 = make_expr "A2" "B" in
  let s3 = make_expr "A3" "C" in
  let s4 = make_expr "A4" "D" in
  let s5 = make_expr "A5" "E" in
  let to_prove = make_stmt "E,B,C" in
  check_proof 5 to_prove [r1] [s1,s2,s3,s4,s5]
  
test4 =
  let r1 = make_ruleset "Free" ["~(~A)-->A","A-->~(~A)","A,B-->B,A","A,B-->A&B"] in
  let r2 = make_ruleset "DL" ["~(A&B)-->~A|~B","~(A|B)-->~A&~B"] in
  let s1 = make_expr "A1" "A&~(B|C)=>C" in
  let to_prove = make_stmt "A&(~B&~C)=>C" in
  check_proof 4 to_prove [r1,r2] [s1]
  
test5 =
  let fr = make_ruleset "Free" ["~(~A)-->A","A,A-->A","A,B-->B,A","A,B-->A&B","A=>B&C-->A=>B"] in
  let tp = make_ruleset "TP" ["A,(A=>B)-->B"] in
  let dl = make_ruleset "DL" ["~(A&B)-->~A|~B","~(A|B)-->~A&~B"] in
  let s1 = make_expr "A1" "~K=>~(Q|M)" in
  let to_prove = make_stmt "~K=>~Q" in
  check_proof 4 to_prove [dl,fr,tp] [s1]
  
test6 =
  let r1 = make_ruleset "Free" ["~(~A)-->A","A-->~(~A)","A,B-->B,A","A,B-->A&B"] in
  let r2 = make_ruleset "DL" ["~(A&B)-->~A|~B","~(A|B)-->~A&~B"] in
  let s1 = make_expr "A1" "~(A&(B|C))=>C" in
  let to_prove = make_stmt "~A|(~B&~C)=>C" in
  check_proof 4 to_prove [r1,r2] [s1]

test7 =
  let r1 = make_ruleset "Free" ["A,B-->B,A"] in
  let r2 = make_ruleset "TP" ["A,(A=>B)-->B"] in
  let s1 = make_expr "A1" "A=>B" in
  let s2 = make_expr "A2" "B=>C" in
  let s3 = make_expr "A3" "C=>D" in
  let s4 = make_expr "A4" "A" in
  let to_prove = make_stmt "C" in
  check_proof 4 to_prove [r1,r2] [s1,s2,s3,s4]
  
run_all = List.map (\f -> (f)) [test1,test2,test3,test4,test5,test6]