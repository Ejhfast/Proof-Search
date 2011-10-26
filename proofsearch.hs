-- Code for proof searching

module ProofSearch where
import Prelude
import List
import qualified Data.Map as Map
import ProofTypes
import ProofParse
import ProofFuncs

-- Placeholder constant to signify failed matching
false_mapping :: [(Stmt String, Stmt String)]
false_mapping = [(Var "T",Free "FALSE"),(Var "T",Free "TRUE")]

-- Search depth for subexpressions
sub_depth_level = 5

--test for consisent substitutions
consistent_subs :: [(Stmt String, Stmt String)] -> [(Stmt String, Stmt String)] -> Bool
consistent_subs lhs rhs =
  let full = lhs ++ rhs in
  let bad_matches = List.map (\(e,f) -> length (List.filter (\(e1,f1) -> (e == e1 && f /= f1) || e /= e1 && f==f1) full)) full in
  case (foldr (+) 0 bad_matches) of
    0 -> True
    _ -> False

--try to match a statement to a rule condition, return mapping of substitutions
match :: Stmt String -> Stmt String -> [(Stmt String, Stmt String)]
match stmt rule =
  case rule of
    Free r1 -> [(stmt,rule)]
    Var "NOP" -> if stmt == (Var "NOP") then [((Var "NOP"),(Var "NOP"))] else false_mapping --hack for unary operations
    Var r1 -> if stmt == (Var r1) then [] else false_mapping -- should not be a Var in rules unless it is a NOP
    (Op ro r1 r2) ->
      case stmt of
        Var s1 -> false_mapping -- Var does not map to statement
        (Op so s1 s2) ->
          case (so == ro) of
            True -> 
              let (lhs, rhs) = ((match s1 r1), (match s2 r2)) in
              case consistent_subs lhs rhs of
                True -> List.nub $ lhs ++ rhs 
                False -> false_mapping -- inconsistent substitutions
            False -> false_mapping -- not the same operator
        Free s1 -> false_mapping --should not a Free in statements

--Replace free variables in a statement as specified in provided mapping
replace_terms :: Stmt String -> [(Stmt String, Stmt String)] -> Stmt String
replace_terms rule lst =
  case rule of
    Var r1 -> Var r1
    Free r1 ->
      let search = List.find (\((e,f)) -> r1 == val f) lst in
      case search of
        Just (e,f) -> e
        Nothing -> Free r1
    (Op ro r1 r2) ->
      (Op ro (replace_terms r1 lst) (replace_terms r2 lst))

all_maps :: Stmt String -> [Expr String] -> [[(Expr String,Stmt String)]]
all_maps stmt facts =
  let frees = get_free_vars stmt in -- [[[(fact1,Free "A")],(fact2,Free "A")...],...[(fact1, Free "N")...]]
  let all_combs = List.map (\e -> [[(y,e)] | y <- facts]) frees in 
  rec_combine all_combs
  
ef2 :: Stmt String -> [Expr String] -> String -> [String] -> [String] -> [Expr String]
ef2 conclusion facts ruleset_name expr_deps r_deps =
  let replacements = all_maps conclusion facts in
  if replacements == [] then [Expr "_" conclusion (Just ([ruleset_name]++r_deps),(Just expr_deps))] else
  [(Expr "_" (replace_terms conclusion (map (\(e,sf) -> (body e, sf)) m)) 
             (Just ([ruleset_name]++r_deps), Just (merge_deps expr_deps (subs_deps m)))) | m <- replacements]
  
-- check for legit expansions... gather list of distinct frees, construct total possible consistent replacings...    
-- Expand free variables into all possible statements
expand_facts :: Stmt String -> [Expr String] -> String -> [String] -> [String] -> [Expr String]
expand_facts conclusion facts ruleset_name expr_deps r_deps =
  case conclusion of 
    Var a -> [Expr "_" (Var a) (Just ([ruleset_name]++r_deps), Just expr_deps)]
    Free a -> facts
    (Op o a b) -> 
      [Expr "_" (Op o (body x) (body y)) (Just ([ruleset_name]++r_deps), Just (merge_deps expr_deps ((deps x)++(deps y))))
          | x <- expand_facts a facts ruleset_name expr_deps r_deps,
            y <- expand_facts b facts ruleset_name expr_deps r_deps ]

-- Generate replacements for top level statement, given a rule and known other statements
match_with_bindings :: Stmt String -> Rule String -> [Expr String] -> String -> [String] -> [String] -> [Expr String]
match_with_bindings stmt rule facts ruleset_name expr_deps r_deps =
  let (cond,conc) = (condition rule, conclusion rule) in
  case match stmt cond of
    [(Var "T",Free "FALSE"),(Var "T",Free "TRUE")] -> [] -- false mapping
    lst -> ef2 (replace_terms conc lst) facts ruleset_name expr_deps r_deps

-- Apply a single rule to statement and get new list of known statements
apply_rule :: Int -> Stmt String -> Rule String -> [Expr String] -> String -> [String] -> [String] -> [Expr String]
apply_rule 0 _ _ _ _ _ _ = []
apply_rule depth stmt rule facts ruleset_name expr_deps r_deps =
    let top_level_match = match_with_bindings stmt rule facts ruleset_name expr_deps r_deps in
    if (kind rule) == "strict" then top_level_match else
    case stmt of
      (Op o lhs rhs) -> --Search inside statements for rule matches
        top_level_match ++ 
        [Expr "_" (Op o (body x) rhs) (Just ([ruleset_name]++r_deps), Just (merge_deps expr_deps (deps x))) 
            | x <- (apply_rule (depth - 1) lhs rule facts ruleset_name expr_deps r_deps)] ++ 
        [Expr "_" (Op o lhs (body x)) (Just ([ruleset_name]++r_deps), Just (merge_deps expr_deps (deps x))) 
            | x <- (apply_rule (depth - 1) rhs rule facts ruleset_name expr_deps r_deps)]
      otherwise -> top_level_match

apply_ruleset :: Expr String -> Ruleset String -> [Expr String] -> [Expr String]
apply_ruleset expr ruleset facts =
  let res = foldr (++) [] [apply_rule sub_depth_level (body expr) r facts (name ruleset) (deps expr) (rule_deps expr)
                          | r <- (set ruleset)] in
  res ++ (f_exprs res)

apply_ruleset_stmts :: [Expr String] -> Ruleset String -> [Expr String]
apply_ruleset_stmts stmts ruleset =
  foldr (++) [] [apply_ruleset s ruleset stmts | s <- stmts]

apply_rulesets :: Expr String -> [Ruleset String] -> [Expr String] -> [Expr String]
apply_rulesets expr rulesets facts =
  foldr (++) [] [apply_ruleset expr rs facts | rs <- rulesets]

apply_rulesets_stmts :: [Expr String] -> [Ruleset String] -> [Expr String]
apply_rulesets_stmts stmts rulesets =
  foldr (++) [] [apply_rulesets s rulesets stmts | s <- stmts]

--Combine expressions pairwise
pairwise_combine :: [Expr String] -> [Expr String]
pairwise_combine facts =
  facts ++ [Expr "_" (Op "," (body x) (body y)) (Just ((rule_deps x)++(rule_deps y)), Just (merge_deps (deps x) (deps y))) 
            | x <- facts, y <- facts]
            
-- Generate all possabilities 
search :: Int -> [Ruleset String] -> [Expr String] -> [Expr String]
search 0 _ stmts = stmts
search depth rulesets stmts = search (depth-1) rulesets $ List.nub $ stmts ++ (apply_rulesets_stmts stmts rulesets)

backward_search :: Int -> Expr String -> [Expr String] -> [Ruleset String] -> [Expr String]
backward_search 0 start stmts _ = [start] ++ stmts
backward_search depth start stmts rulesets = -- reverse direction of rulesets
  let rev_rules = map (\rs -> let r_set = map (\r -> (Rule (conclusion r) (condition r) (kind r))) (set rs) in (Ruleset (name rs) r_set)) rulesets in 
  let newstmts = List.nub $ (apply_rulesets start rev_rules stmts) in
  backward_search (depth - 1) start newstmts rulesets

verify :: Int -> Stmt String -> [Ruleset String] -> [Expr String] -> Maybe String
verify depth stmt rulesets assumps =
  let equiv = backward_search 1 (Expr "GOAL" stmt (Nothing,Nothing)) assumps rulesets in -- find things equivalent to the goal
  check_proof depth equiv rulesets assumps

check_proof :: Int -> [Expr String] -> [Ruleset String] -> [Expr String] -> Maybe String
check_proof 0 _ _ stmts = Nothing
check_proof depth toprove rulesets stmts = 
  let update = stmts ++ apply_rulesets_stmts stmts rulesets in
  let res = contains toprove update in
  case res of 
    ((x,y):rst) -> Just ("Forward: "++(show_expr y)++" "++"Backward: "++(show_expr x))
    _ -> check_proof (depth - 1) toprove rulesets $ pairwise_combine $ List.nub update