module ProofSearch where
import Prelude
import List
import qualified Data.Map as Map
import ProofTypes
import ProofParse
import ProofFuncs

sub_depth_level = 15 -- Search depth for subexpressions

--test for consisent substitutions
consistent_subs :: [(Stmt String, Stmt String)] -> [(Stmt String, Stmt String)] -> Bool
consistent_subs lhs rhs = if (sum bad_matches) == 0 then True else False 
  where 
    full = lhs ++ rhs
    bad_matches = map (\(e,f) -> length (filter (\(e1,f1) -> e /= e1 && f==f1) full)) full -- (e == e1 && f /= f1) || 

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

-- match rules with two conditions
multi_match :: Stmt String -> Stmt String -> Stmt String -> [Expr String] -> [String] -> [String] -> [Stmt String] -> [Expr String]
multi_match cond conc stmt facts expr_deps r_deps cons = case cond of
  (Op "," a b) -> case (match stmt a) of
    [(Var "FALSE",Free "T"),(Var "TRUE",Free "T")] -> []
    l_subs -> let r_sub_lst = filter (\(f,d)-> ((f /= false_mapping) && (consistent_subs l_subs f))) [(match (body x) b,(deps x)) | x <- facts] in
      [Expr "_" (replace_terms conc (l_subs ++ r_subs) cons) (Just r_deps, Just (merge_deps expr_deps d)) | (r_subs, d) <- r_sub_lst ]

find_constraint :: String -> Stmt String -> Bool
find_constraint free cons =
  case cons of
    Op "CONSTRAINT" (Var s) c -> (s == free)
    _ -> False

meet_constraint :: String -> Stmt String -> [Stmt String] -> Bool
meet_constraint free_nm try_mat cons = 
  let match = List.find (find_constraint free_nm) cons in
  case try_mat of
    Var p_mat ->
      case match of 
        Just (Op "CONSTRAINT" (Var n) c) ->
          let t1 = (reads p_mat :: [(Int,String)]) in
          case t1 of
            [(int1,_)] ->
              case c of
                Op "=" (Var m) (Var n) ->
                  let t2 = (reads p_mat :: [(Int,String)]) in
                    case t2 of
                      [(int2,_)] -> if (m == n) && (int1 == int2) then True else False
                      _ -> True
                Op "!=" (Var m) (Var n) ->
                  let t2 = (reads p_mat :: [(Int,String)]) in
                    case t2 of
                      [(int2,_)] -> if (m == n) && (int1 /= int2) then True else False
                      _ -> True
                _ -> True
            _ -> True
        _ -> True
    _ -> True -- too complicated for now ;)

--Replace free variables in a statement as specified in provided mapping
replace_terms :: Stmt String -> [(Stmt String, Stmt String)] -> [Stmt String] -> Stmt String
replace_terms rule lst cons =
  case rule of
    Var r1 -> Var r1
    Free r1 -> let search = List.find (\((e,f)) -> r1 == val f) lst in
      case search of
        Just (e,f) -> if meet_constraint r1 e cons then e else Free r1
        Nothing -> Free r1
    (Op ro r1 r2) ->
      (Op ro (replace_terms r1 lst cons) (replace_terms r2 lst cons))

-- Expand free variables, maintaining consistancy (e.g. for each possible expansion, "A" mapped everywhere to same value)
expand :: Stmt String -> [Expr String] -> String -> [String] -> [String] -> [Stmt String] -> [Expr String]
expand conclusion facts ruleset_name expr_deps r_deps cons =
  let frees = get_free_vars conclusion in
  let all_combs = List.map (\e -> [[(y,e)] | y <- facts]) frees in
  let replacements = rec_combine all_combs in -- Generate all possible mappings
  if replacements == [] then [Expr "_" conclusion (Just ([ruleset_name]++r_deps),(Just expr_deps))] else
    [(Expr "_" (replace_terms conclusion (map (\(e,sf) -> (body e, sf)) m) cons) 
             (Just ([ruleset_name]++r_deps), Just (merge_deps expr_deps (subs_deps m)))) | m <- replacements]

-- Apply a single rule to statement and get new list of known statements
apply_rule :: Int -> Stmt String -> Rule String -> [Expr String] -> String -> [String] -> [String] -> [Expr String]
apply_rule 0 _ _ _ _ _ _ = []
apply_rule depth stmt rule facts ruleset_name expr_deps r_deps =
  let (cond,conc) = (condition rule, conclusion rule) in
  let try_match = (match stmt cond) in
  let cons = (cnst rule) in
  let top_level_match = if try_match == false_mapping then [] else expand (replace_terms conc try_match cons) facts ruleset_name expr_deps r_deps cons in
  case cond of
    (Op "," _ _) -> multi_match cond conc stmt facts expr_deps (ruleset_name:r_deps) cons
    otherwise ->
      case (kind rule) of
        Equality -> -- with equality, recursive
          case stmt of
            (Op o lhs rhs) -> --Search inside statements for rule matches
              top_level_match ++
              [Expr "_" (Op o (body x) rhs) (Just ([ruleset_name]++r_deps), Just (merge_deps expr_deps (deps x))) 
                | x <- (apply_rule (depth - 1) lhs rule facts ruleset_name expr_deps r_deps)] ++ 
              [Expr "_" (Op o lhs (body x)) (Just ([ruleset_name]++r_deps), Just (merge_deps expr_deps (deps x))) 
                | x <- (apply_rule (depth - 1) rhs rule facts ruleset_name expr_deps r_deps)]
            otherwise -> top_level_match
        otherwise -> top_level_match -- just rewrites allowed       
        
-- generate rule expansions/rewrites...

apply_ruleset :: Expr String -> Ruleset String -> [Expr String] -> [Expr String]
apply_ruleset expr ruleset facts =
  concat [f_exprs $ apply_rule sub_depth_level (body expr) r facts (name ruleset) (deps expr) (rule_deps expr) | r <- (set ruleset)]

apply_ruleset_stmts :: [Expr String] -> Ruleset String -> [Expr String]
apply_ruleset_stmts stmts ruleset = concat [apply_ruleset s ruleset stmts | s <- stmts]

apply_rulesets :: Expr String -> [Ruleset String] -> [Expr String] -> [Expr String]
apply_rulesets expr rulesets facts = concat [apply_ruleset expr rs facts | rs <- rulesets]

apply_rulesets_stmts :: [Expr String] -> [Ruleset String] -> [Expr String]
apply_rulesets_stmts stmts rulesets = 
  case rulesets of 
    [] -> f_exprs stmts
    _ -> concat [apply_rulesets s rulesets stmts | s <- stmts]

back_apply_rulesets_stmts :: [Expr String] -> [Ruleset String] -> [Expr String]
back_apply_rulesets_stmts stmts rulesets = 
  case rulesets of
    [] -> f_exprs stmts
    _ -> concat [apply_rulesets s (rev_rules rulesets) stmts | s <- stmts]

rev_rules :: [Ruleset String] -> [Ruleset String]
rev_rules rsets = 
  map (\rs -> Ruleset (name rs) (map (\r -> Rule (conclusion r) (condition r) (kind r) (cnst r)) $ set rs)) rsets