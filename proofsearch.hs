module ProofSearch where
import Prelude
import List
import qualified Data.Map as Map
import ProofTypes
import ProofParse
import ProofFuncs

sub_depth_level = 5 -- Search depth for subexpressions

--test for consisent substitutions
consistent_subs :: [(Stmt String, Stmt String)] -> [(Stmt String, Stmt String)] -> Bool
consistent_subs lhs rhs =
  let full = lhs ++ rhs in
  let bad_matches = List.map (\(e,f) -> length (List.filter (\(e1,f1) -> (e == e1 && f /= f1) || e /= e1 && f==f1) full)) full in
  if (foldr (+) 0 bad_matches) == 0 then True else False

--try to match a statement to a rule condition, return mapping of substitutions
match :: Stmt String -> Stmt String -> [(Stmt String, Stmt String)]
match stmt rule =
  case rule of
    Free r1 -> [(stmt,rule)]
    Var "NOP" -> if stmt == (Var "NOP") then [((Var "NOP"),(Var "NOP"))] else false_mapping --hack for unary operations
    Var r1 -> if stmt == (Var r1) then [] else false_mapping
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
    Free r1 -> let search = List.find (\((e,f)) -> r1 == val f) lst in
      case search of
        Just (e,f) -> e
        Nothing -> Free r1
    (Op ro r1 r2) ->
      (Op ro (replace_terms r1 lst) (replace_terms r2 lst))

-- Expand free variables, maintaining consistancy (e.g. for each possible expansion, "A" mapped everywhere to same value)
expand :: Stmt String -> [Expr String] -> String -> [String] -> [String] -> [Expr String]
expand conclusion facts ruleset_name expr_deps r_deps =
  let frees = get_free_vars conclusion in
  let all_combs = List.map (\e -> [[(y,e)] | y <- facts]) frees in
  let replacements = rec_combine all_combs in -- Generate all possible mappings
  if replacements == [] then [Expr "_" conclusion (Just ([ruleset_name]++r_deps),(Just expr_deps))] else
  [(Expr "_" (replace_terms conclusion (map (\(e,sf) -> (body e, sf)) m)) 
             (Just ([ruleset_name]++r_deps), Just (merge_deps expr_deps (subs_deps m)))) | m <- replacements]

-- Apply a single rule to statement and get new list of known statements
apply_rule :: Int -> Stmt String -> Rule String -> [Expr String] -> String -> [String] -> [String] -> [Expr String]
apply_rule 0 _ _ _ _ _ _ = []
apply_rule depth stmt rule facts ruleset_name expr_deps r_deps =
  let (cond,conc) = (condition rule, conclusion rule) in
  let try_match = (match stmt cond) in
  let top_level_match = if try_match == false_mapping then [] else expand (replace_terms conc try_match) facts ruleset_name expr_deps r_deps in
  case (kind rule) of
    Strict -> top_level_match -- just rewrites allowed
    Unconditional -> expand conc facts ruleset_name expr_deps r_deps -- nothing for the rule to match
    Equality -> -- with equality, recursive
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
  (foldr (++) [] [f_exprs $ apply_rule sub_depth_level (body expr) r facts (name ruleset) (deps expr) (rule_deps expr)
                | r <- (set ruleset)])

apply_ruleset_stmts :: [Expr String] -> Ruleset String -> [Expr String]
apply_ruleset_stmts stmts ruleset =
  foldr (++) [] [apply_ruleset s ruleset stmts | s <- stmts]

apply_rulesets :: Expr String -> [Ruleset String] -> [Expr String] -> [Expr String]
apply_rulesets expr rulesets facts =
  foldr (++) [] [apply_ruleset expr rs facts | rs <- rulesets]

apply_rulesets_stmts :: [Expr String] -> [Ruleset String] -> [Expr String]
apply_rulesets_stmts stmts rulesets =
  foldr (++) [] [apply_rulesets s rulesets stmts | s <- stmts]

backward_search :: Int -> Expr String -> [Expr String] -> [Ruleset String] -> [Expr String]
backward_search 0 start stmts _ = [start] ++ stmts
backward_search depth start stmts rulesets = -- reverse direction of rulesets
  let rev_rules = map (\rs -> Ruleset (name rs) (map (\r -> Rule (conclusion r) (condition r) (kind r)) $ set rs) (descrip rs)) rulesets in 
  let newstmts = List.nub $ apply_rulesets start rev_rules stmts in
  backward_search (depth - 1) start newstmts rulesets