module ProofFuncs where
import List  
import ProofTypes

math :: (Int -> Int -> Int) -> String -> String -> String
math f x y =
	let (xn,yn) = (read x :: Int, read y :: Int) in
	show $ f xn yn
	
str_to_lst :: Stmt String -> [Stmt String]
str_to_lst stmt =
  case stmt of
    (Op "." x y) -> (str_to_lst x) ++ (str_to_lst y)
    Var x -> [Var x]
    Free y -> [Free y]
    
lst_to_stmt :: [Stmt String] -> Stmt String
lst_to_stmt (x:[]) = x
lst_to_stmt (x:xs) = (Op "." x (lst_to_stmt xs))

string_order :: Stmt String -> Stmt String
string_order stmt = lst_to_stmt $ str_to_lst stmt

collapse_funcs :: Stmt String -> Stmt String
collapse_funcs stmt =
	case stmt of
		(Var x) -> stmt
		(Free x) -> stmt
		(Op op (Var x) (Var y)) -> case op of
			"+" -> (Var (math (+) x y))
			"-" -> (Var (math (-) x y))
			"*" -> (Var (math (*) x y ))
			_ -> stmt
		(Op op lhs rhs) -> (Op op (collapse_funcs lhs) (collapse_funcs rhs))
		
f_expr :: Expr String -> Expr String
f_expr expr =
	let stmt = (body expr) in
	Expr (_id expr) (collapse_funcs stmt) (justification expr)

f_exprs :: [Expr String] -> [Expr String]
f_exprs exprs =
	List.map f_expr exprs