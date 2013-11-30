module ProofTypes where
import Prelude
import Data.List

-- An Expr is a "fact" in the system
data Expr a = Expr {
  _id :: String,
  body :: Stmt a,
  justification :: (
    Maybe [String],
    Maybe [String])
  }
  deriving (Show, Eq)
-- Stmts recursively describe an expression
data Stmt a = Op a (Stmt a) (Stmt a) | Var a | Free a
  deriving (Show, Eq)
-- Rules rewrite a condition into a conclusion
data Rule a = Rule {
  condition :: Stmt a,
  conclusion :: Stmt a,
  kind :: Kind,
  cnst :: [Stmt a]
  }
  deriving (Show, Eq)
-- Rules can be strict rewrites, equalities, or notions of fact combination
data Kind = Equality | Strict | Unconditional deriving (Show, Eq)
-- A Ruleset is a named set of rules
data Ruleset a = Ruleset {name :: String, set :: [Rule a]}
  deriving (Show, Eq)

-- Placeholder constant to signify failed matching of rule
falseMapping = [(
                    Var "FALSE",
                    Free "T"),
                 (
                   Var "TRUE",
                   Free "T")]

-- Get the name of a statement leaf
val :: Stmt String -> String
val stmt = case stmt of
  Var a -> a
  Free a -> a
  otherwise -> "STATEMENT" -- should not happen

-- Get assumptions assosiated with an expression
deps :: Expr String -> [String]
deps expr =
  case justification expr of
    (_, Just a) -> nub $
                   filter (
                     /= "_"
                     )
                   (
                     a ++ [
                        _id expr
                        ]
                   )
    (_, Nothing) -> [_id expr]

-- Get rules used to prove an expression
ruleDeps :: Expr String -> [String]
ruleDeps expr =
  case justification expr of
    (Just a, _) -> a
    (Nothing, _ ) -> []

-- Merge two lists of expression assumptions
mergeDeps :: [String] -> [String] -> [String]
mergeDeps one two = nub $ one ++ two

-- get all assumption dependencies associated with a rule expansion
subsDeps :: [
  (
    Expr String,
    Stmt String
  )
  ] -> [String]
subsDeps lst = concat [
  deps expr |
  (expr, free) <- lst
              ]

-- given two lists of expressions, find those that make equivalent statements
contains :: [Expr String] ->
            [Expr String] ->
            [(Expr String, Expr String)]
contains lst1 lst2 =
  [
    (x , y)
  |
    x <- lst1,
    y <- lst2,
    body x == body y
  ]

-- get all free variables in a rule/statement
getFreeVars :: Stmt String -> [Stmt String]
getFreeVars stmt = case stmt of
  (Free a) -> [Free a]
  (Var a) -> []
  (Op _ x y) -> nub $ getFreeVars x ++ getFreeVars y

-- helper method for generating all possible rule expansions
recCombine :: [[[a]]] -> [[a]]
recCombine (l1 : l2 : rest) = recCombine (
  [
    x
    ++
    y
  |
    x <- l1,
    y <- l2
  ] : rest
  )

recCombine (
  l1 : []
  ) = l1
recCombine _ = []

-- Helpers to prettify expressions

showStmt :: Stmt String -> String
showStmt stmt =
  case stmt of
    (Op o a (Var "NOP")) ->
      o ++ showStmt a
    (Op "." a b) -> showStmt a
                    ++ "." ++
                    showStmt b
    (Op o a b) -> "(" ++
                  showStmt a
                  ++ o ++
                  showStmt b
                  ++ ")"
    (Var a) -> a
    (Free a) -> a



showExpr :: Expr String -> String
showExpr expr =
  filter (/= '\"')  (showStmt $ body expr)
  ++
  " by rule(s) "
  ++
  show (ruleDeps expr)
  ++
  " and assumption(s) "
  ++
  show (deps expr)
  