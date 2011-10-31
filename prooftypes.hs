module ProofTypes where
import Prelude
import List

-- An Expr is a "fact" in the system
data Expr a = Expr {_id :: String, body :: Stmt a, justification :: (Maybe [String], Maybe [String])}
  deriving (Show,Eq)
-- Stmts recursively describe an expression
data Stmt a = Op a (Stmt a) (Stmt a) | Var a | Free a
  deriving (Show,Eq)
-- Rules rewrite a condition into a conclusion
data Rule a = Rule {condition :: Stmt a, conclusion :: Stmt a, kind :: Kind}
  deriving (Show, Eq)
-- Rules can be strict rewrites, equalities, or notions of fact combination
data Kind = Equality | Strict | Unconditional deriving (Show,Eq)
-- A Ruleset is a named set of rules
data Ruleset a =  Ruleset {name :: String, set :: [Rule a], descrip :: String}
  deriving (Show, Eq)

-- Placeholder constant to signify failed matching of rule
false_mapping = [(Var "T",Free "FALSE"),(Var "T",Free "TRUE")]

-- Get the name of a statement leaf
val :: Stmt String -> String
val stmt = case stmt of
  Var a -> a
  Free a -> a
  otherwise -> "STATEMENT" -- should not happen

--Get assumptions assosiated with an expression
deps :: Expr String -> [String]
deps expr =
  case justification expr of
    (_, Just a) -> List.nub $ filter (\a -> a /= "_") (a++[_id expr])
    (_, Nothing) -> [_id expr]

--Get rules used to prove an expression
rule_deps :: Expr String -> [String]
rule_deps expr =
  case justification expr of
    (Just a, _) -> a
    (Nothing,_) -> []

--Merge two lists of expression assumptions
merge_deps :: [String] -> [String] -> [String]
merge_deps one two = List.nub $ one ++ two

--get all assumption dependencies associated with a rule expansion
subs_deps :: [(Expr String,Stmt String)] -> [String]
subs_deps lst = concat [(deps expr) | (expr,free) <- lst]

--given two lists of expressions, find those that make equivalent statements
contains :: [Expr String] -> [Expr String] -> [(Expr String,Expr String)]
contains lst1 lst2 =
  [ (x,y) | x <- lst1, y <- lst2, (body x) == (body y)]

--get all free variables in a rule/statement
get_free_vars :: Stmt String -> [Stmt String]
get_free_vars stmt = case stmt of 
  (Free a) -> [Free a]
  (Var a) -> []
  (Op _ x y) -> List.nub $ (get_free_vars x) ++ (get_free_vars y)

--helper method for generating all possible rule expansions    
rec_combine :: [[[a]]] -> [[a]]
rec_combine (l1:l2:rest) = rec_combine ([x++y | x <- l1, y <- l2]:rest)
rec_combine (l1:[]) = l1
rec_combine _ = []

--Helpers to prettify expressions

show_stmt :: Stmt String -> String
show_stmt stmt = 
  case stmt of
    (Op o a (Var "NOP")) -> o++(show_stmt a)
    (Op "." a b) -> (show_stmt a) ++ "." ++ (show_stmt b)
    (Op o a b) -> "("++(show_stmt a) ++ o ++ (show_stmt b)++")"
    (Var a) -> a
    (Free a) -> a
    
show_expr :: Expr String -> String
show_expr expr =
  filter (\c -> c /= '\"') $ (show_stmt $ body expr)++" by rule(s) "++
    (show (rule_deps expr))++" and assumption(s) "++(show (deps expr))