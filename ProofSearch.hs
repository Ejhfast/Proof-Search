module ProofSearch where
import Prelude
import Data.List
import Debug.Trace
import qualified Data.Map as Map
import ProofTypes
import ProofParse
import ProofFuncs

subDepthLevel = 12 -- Search depth for subexpressions

-- test for consisent substitutions
consistentSubs :: [
  (
    Stmt String,
    Stmt String
  )
  ] -> [
  (
    Stmt String,
    Stmt String
  )
  ] -> Bool
consistentSubs lhs rhs =
  sum bad_matches == 0
  where
    full = lhs ++ rhs
    bad_matches = map (
      \ ( e , f ) ->
      length (filter (
                 \ (
                   e1,
                   f1
                  ) ->
                 e /= e1
                 &&
                 f == f1
                 )
              full
             )
      ) full

-- try to match a statement to a rule condition, return mapping of substitutions
match :: Stmt String ->
         Stmt String ->
         [Stmt String] ->
         [(Stmt String, Stmt String)]
match stmt rule cons =
  case rule of
    Free r1 -> if meet_constraint r1 stmt cons
               then [
                 (stmt , rule)
                 ]
               else
                 false_mapping
    Var "NOP" ->
      if stmt == Var "NOP"
      then []
      else false_mapping -- hack for unary operations
    Var r1 ->
      if stmt == Var r1
      then []
      else false_mapping
    (Op ro r1 r2) ->
      case stmt of
        Var s1 -> false_mapping -- Var does not map to statement
        (Op so s1 s2) ->
          if so == ro then
             (
              let (lhs, rhs) =
                    (
                      match s1 r1 cons,
                      match s2 r2 cons
                    )
              in
              if consistent_subs lhs rhs then
                nub $ lhs ++ rhs
                else
                false_mapping -- inconsistent substitutions
             )
             else false_mapping -- not the same operator
        Free s1 -> false_mapping -- should not a Free in statements

-- match rules with two conditions
multiMatch :: Stmt String ->
               Stmt String -> Stmt String ->
               [Expr String] ->
               [String] ->
               [String] ->
               [Stmt String] ->
               [Expr String]
multiMatch cond conc stmt facts expr_deps r_deps cons = case cond of
  (Op "," a b) ->
    case match stmt a cons of
    [(
        Var "FALSE",
        Free "T"),
     (
       Var "TRUE",
       Free "T")
      ] -> []
    l_subs -> let r_sub_lst =
                    filter (
                      \ (f, d) ->
                      ((f /= false_mapping) &&
                       consistent_subs l_subs f))
                    [
                      (match (body x) b cons,
                       deps x
                      )
                    |
                     x <- facts] in
      [Expr "_" (replace_terms conc (
                    l_subs ++ r_subs) cons)
       (Just r_deps,
        Just (merge_deps expr_deps d))
      | (r_subs, d)
                    <- r_sub_lst ]

findConstraint :: String -> Stmt String -> Bool
findConstraint free cons =
  case cons of
    Op "CONSTRAINT" (Var s) c -> s == free
    _ -> False

meetConstraint :: String -> Stmt String -> [Stmt String] -> Bool
meetConstraint free_nm try_mat cons =
  let match = find (find_constraint free_nm) cons in
  case try_mat of
    Var p_mat ->
      case match of
        Just (Op "CONSTRAINT" (Var n)
              (Op "__CNTS" x (Var "NOP"))) ->
          contains_var x (Var p_mat)
        Just (
          Op "CONSTRAINT" (Var n)
          (Op "__NOT_CNTS" x (Var "NOP"))) ->
          Debug.Trace.trace (
            show (
               not (
                  contains_var x (Var p_mat))))
          (not (contains_var x (Var p_mat)))
        _ -> True
    stmt ->
      case match of
        Just (Op "CONSTRAINT" (Var n)
              (Op "__CNTS" x (Var "NOP"))) -> contains_var x stmt
        Just (Op "CONSTRAINT" (Var n)
              (Op "__NOT_CNTS" x (Var "NOP"))) ->
          Debug.Trace.trace (show (not (contains_var x stmt)))
          (not (contains_var x stmt))
        _ -> True

containsVar :: Stmt String -> Stmt String -> Bool
containsVar sub_expr expr =
  case
    Debug.Trace.trace (
      "Expr: " ++
      show expr
      ++ "\nSubExpr: " ++
      show sub_expr
      ) expr
  of
    Var x -> sub_expr == expr
    Free x -> sub_expr == expr
    Op o x y -> contains_var sub_expr x
                ||
                contains_var sub_expr y

-- Replace free variables in a statement as specified in provided mapping
replaceTerms ::
  Stmt String -> [(Stmt String, Stmt String)] -> [Stmt String] -> Stmt String
replaceTerms rule lst cons =
  case rule of
    Var r1 -> Var r1
    Free r1 -> let search = find (
                     \ (
                       (e ,
                        f)
                       ) ->
                     r1 == val f
                     ) lst in
      case search of
        Just (
          e
               ,
          f
               ) ->
          if meet_constraint r1 e cons
          then e
          else Var "FAIL" -- Free r1
        Nothing -> Free r1
    (Op ro r1 r2) ->
      let lhs = replace_terms r1 lst cons in
      let rhs = replace_terms r2 lst cons in
      case (lhs, rhs )
      of
        (Var "FAIL", Var "FAIL") -> Var "FAIL"
        (Var "FAIL", _) -> Var "FAIL"
        (_, Var "FAIL") -> Var "FAIL"
        _ -> Op ro lhs rhs
{-
 Expand free variables, maintaining consistancy
 (e.g. for each possible expansion, "A" mapped everywhere to same value)
-}
expand :: Stmt String ->
          [Expr String] ->
          String ->
          [String] ->
          [String] ->
          [Stmt String] ->
          [Expr String]
expand conclusion facts ruleset_name expr_deps r_deps cons =
  let frees = get_free_vars conclusion in
  let all_combs = map (
        \ e -> [
          [
            (
              y
               ,
              e
            )
          ]
          |
          y <- facts
          ]
        ) frees in
  let replacements = rec_combine all_combs in -- Generate all possible mappings
  if null replacements then
    (if conclusion ==
        Var "FAIL"
     then []
     else [
       Expr "_" conclusion (
          Just ( ruleset_name : r_deps ),
          Just expr_deps)]) else
    filter (
      \ a -> body a /= Var "FAIL"
      )
    [
      Expr "_" (
         replace_terms conclusion (
            map (
               ControlArrow.first body
               ) m
            ) cons
         )
      (
        Just (ruleset_name : r_deps),
        Just (merge_deps expr_deps (
                 subs_deps m)
             )
      )
      |
      m <- replacements]

-- Apply a single rule to statement and get new list of known statements
applyRule :: Int ->
              Stmt String ->
              Rule String ->
              [Expr String] ->
              String ->
              [String] ->
              [String] ->
              [Expr String]
applyRule 0 _ _ _ _ _ _ = []
applyRule depth stmt rule facts ruleset_name expr_deps r_deps =
  let (cond, conc) = (
        condition rule, conclusion rule
        ) in
  let cons = cnst rule in
  let try_match = match stmt cond cons in
  let prelim_expand = replace_terms conc try_match cons in
    let top_level_match
          = if try_match == false_mapping then [] else
              expand prelim_expand facts ruleset_name expr_deps r_deps cons
      in
      case cond of
          (Op "," _ _) -> multi_match cond conc stmt facts expr_deps
                            (ruleset_name : r_deps)
                            cons
          otherwise ->
              case kind rule of
                Equality -> case stmt of
                      (Op o lhs rhs) -> top_level_match ++
                                          [Expr "_" (Op o (body x) rhs)
                                             (
                                               Just (ruleset_name : r_deps),
                                               Just (merge_deps expr_deps
                                                     (deps x)))
                                           |
                                           x <-
                                             apply_rule (depth - 1)
                                             lhs rule facts ruleset_name
                                             expr_deps
                                             r_deps]
                                            ++
                                            [
                                              Expr "_" (Op o lhs (body x))
                                               (Just (ruleset_name : r_deps),
                                                Just (merge_deps expr_deps
                                                      (deps x)))
                                            |
                                             x <-
                                               apply_rule (depth - 1)
                                               rhs rule facts ruleset_name
                                               expr_deps
                                               r_deps
                                             ]

                      otherwise -> top_level_match
                otherwise -> top_level_match


-- generate rule expansions/rewrites...

applyRuleset :: Expr String -> Ruleset String -> [Expr String] -> [Expr String]
applyRuleset expr ruleset facts =
  concat [
    f_exprs $
    apply_rule
    sub_depth_level (body expr)
    r facts (name ruleset)
    (deps expr)
    (
      rule_deps expr
    )
    |
    r <- set ruleset
    ]

applyRulesetStmts :: [Expr String] -> Ruleset String -> [Expr String]
applyRulesetStmts stmts ruleset =
  concat [
    apply_ruleset s ruleset stmts
    |
    s <- stmts]

applyRulesets :: Expr String ->
                  [Ruleset String] ->
                  [Expr String] ->
                  [Expr String]
applyRulesets expr rulesets facts =
  concat [
    apply_ruleset expr rs facts
    | rs <- rulesets]

applyRulesetsStmts :: [Expr String] -> [Ruleset String] -> [Expr String]
applyRulesetsStmts stmts rulesets =
  case rulesets of
    [] -> f_exprs stmts
    _ -> concat [apply_rulesets s rulesets stmts | s <- stmts]

backApplyRulesetsStmts :: [Expr String] -> [Ruleset String] -> [Expr String]
backApplyRulesetsStmts stmts rulesets =
  case rulesets of
    [] -> f_exprs stmts
    _ -> concat [apply_rulesets s (rev_rules rulesets) stmts | s <- stmts]

revRules :: [Ruleset String] -> [Ruleset String]
revRules = map
          (\ rs ->
           Ruleset (name rs)
             (map (\ r -> Rule (conclusion r) (condition r) (kind r) (cnst r)) $
                set rs)) rsets
