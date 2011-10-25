module ProofFuncs where
import List  
import ProofTypes

math :: (Int -> Int -> Int) -> String -> String -> String
math f x y =
	let (xn,yn) = (read x :: Int, read y :: Int) in
	show $ f xn yn

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