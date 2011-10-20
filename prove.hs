module ProofSearch where
import Prelude
import List
import System.Random
import qualified Data.Map as Map

data Expr a = Expr {id :: String, body :: Stmt a}
  deriving (Show, Eq)
data Stmt a = Op a (Stmt a) (Stmt a) | Var a | Free a
  deriving (Show, Eq)
data Rule a = Rule {condition :: Stmt a, conclusion :: Stmt a}
  deriving (Show, Eq)
data Ruleset a =  Ruleset {name :: String, set :: [Rule a]}

-- Get the name of a statement leaf
val :: Stmt String -> String
val stmt =
  case stmt of
    Var a -> a
    Free a -> a
    otherwise -> "STATEMENT" -- should not happen

--test for consisent substitutions
consistent_subs :: [(Stmt String, Stmt String)] -> [(Stmt String, Stmt String)] -> Bool
consistent_subs lhs rhs =
  let bad_matches = List.map (\(e,f) -> length (List.filter (\(e1,f1) -> e == e1 && f /= f1) rhs)) lhs in
  case (foldr (+) 0 bad_matches) of
    0 -> True
    _ -> False

--try to match a statement to a rule condition, return mapping of substitutions
match :: Stmt String -> Stmt String -> [(Stmt String, Stmt String)]
match stmt rule =
  case rule of
    Free r1 -> [(stmt,rule)]
    Var r1 -> [] -- should not be a Var in rules
    (Op ro r1 r2) ->
      case stmt of
        Var s1 -> [] -- Var does not map to statement
        (Op so s1 s2) -> 
          case (so == ro) of
            True -> 
              let (lhs, rhs) = ((match s1 r1), (match s2 r2)) in
              case consistent_subs lhs rhs of
                True -> List.nub $ lhs ++ rhs 
                False -> [] -- inconsistent substitutions
            False -> [] -- not the same operator
        Free s1 -> [] --should not a Free in statements

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
    
-- Expand free variables into all possible known statements
expand_facts :: Stmt String -> [Stmt String] -> [Stmt String]
expand_facts conclusion facts =
  case conclusion of 
    Var a -> [Var a]
    Free a -> facts
    (Op o a b) -> [Op o x y | x <- expand_facts a facts, y <- expand_facts b facts ]

-- Generate replacements for top level statement, given a rule and known other statements
match_with_bindings :: Stmt String -> Rule String -> [Stmt String] -> [Stmt String]
match_with_bindings stmt rule facts =
  let (cond,conc) = (condition rule, conclusion rule) in
  case match stmt cond of
    [] -> facts
    lst -> expand_facts (replace_terms conc lst) facts

-- Apply a single rule to statement and get new list of known statements
apply_rule :: Int -> Stmt String -> Rule String -> [Stmt String] -> [Stmt String]
apply_rule depth stmt rule facts =
  case depth of 
    0 -> []
    _ ->
      let top_level_match = match_with_bindings stmt rule facts in
      case stmt of
        (Op o lhs rhs) -> --Search inside statements for rule matches
          top_level_match ++ 
          [(Op o x rhs) | x <- (apply_rule (depth - 1) lhs rule facts)] ++ 
          [(Op o lhs x) | x <- (apply_rule (depth - 1) rhs rule facts)]
        otherwise -> top_level_match

apply_ruleset :: Stmt String -> Ruleset String -> [Stmt String] -> [Stmt String]
apply_ruleset stmt ruleset facts =
  foldr (++) [] [apply_rule 2 stmt r facts | r <- (set ruleset)] --harcoded depth two, subexpressions

apply_ruleset_stmts :: [Stmt String] -> Ruleset String -> [Stmt String]
apply_ruleset_stmts stmts ruleset =
  foldr (++) [] [apply_ruleset s ruleset stmts | s <- stmts]

apply_rulesets :: Stmt String -> [Ruleset String] -> [Stmt String] -> [Stmt String]
apply_rulesets stmt rulesets facts =
  foldr (++) [] [apply_ruleset stmt rs facts | rs <- rulesets]

apply_rulesets_stmts :: [Stmt String] -> [Ruleset String] -> [Stmt String]
apply_rulesets_stmts stmts rulesets =
  foldr (++) [] [apply_rulesets s rulesets stmts | s <- stmts]
  
search :: Int -> [Stmt String] -> [Ruleset String] -> [Stmt String]
search 0 stmts _ = stmts 
search depth stmts rulesets =
  let update_stmts = apply_rulesets_stmts stmts rulesets in
  search (depth - 1) (List.nub (update_stmts ++ stmts)) rulesets
  
check_proof :: Int -> Stmt String -> Ruleset String -> [Ruleset String] -> [Stmt String] -> Maybe (Stmt String)
check_proof 0 proof ruleset rulesets stmts = 
  let with_rule = apply_ruleset_stmts stmts ruleset in
  let res = List.find (\l -> l == proof) with_rule in
  case res of 
    Just el -> res
    Nothing -> Nothing
check_proof depth proof ruleset rulesets assumptions =
    let new_stmts = apply_rulesets_stmts assumptions rulesets in --free rules
    check_proof (depth-1) proof ruleset rulesets new_stmts
    
  
test =
  let cond1 = Op "AND" (Free "A") (Op "=>" (Free "A") (Free "B")) in
  let conc1 = (Free "B") in
  let r1 = Rule cond1 conc1 in
  let cond2 = (Free "A") in
  let conc2 = Op "AND" (Free "A") (Free "B") in
  let r2 = Rule cond2 conc2 in
  let cond3 = Op "AND" (Free "A") (Free "B") in
  let conc3 = Op "AND" (Free "B") (Free "A") in
  let r3 = Rule cond3 conc3 in
  let rs1 = Ruleset "Free" [r2,r3] in
  let rs2 = Ruleset "PP" [r1] in
  let s1 = Op "=>" (Var "B") (Var "C") in
  let s2 = Op "=>" (Var "C") (Var "D") in
  let s3 = Op "=>" (Var "D") (Var "E") in
  let s4 = Op "=>" (Var "E") (Var "F") in
  let s5 = Op "=>" (Var "F") (Var "G") in
  let s6 = Op "=>" (Var "G") (Var "H") in
  let s7 = Op "=>" (Var "H") (Var "I") in
  let s8 = Var "B" in
  let s9 = Op "OR" (Op "AND" (Var "A") (Var "B")) (Op "OR" (Var "F") (Var "G")) in
  let s10 = Op "AND" (Var "L") (Var "M") in
  check_proof 2 (Var "I") rs2 [rs1] [s8,s1,s2,s3,s4,s5,s6,s7]

  
  
  
  
  