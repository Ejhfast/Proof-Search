module ProofFuncs where
import Data.List  
import ProofTypes

math :: (Int -> Int -> Int) -> String -> String -> String -> Stmt String
math f sym x y =
	let (xn,yn) = (reads x :: [(Int,String)], reads y :: [(Int,String)]) in
	case xn of
	  [(xint,_)] ->
	   case yn of
	     [(yint,_)] -> (Var (show $ f xint yint))
	     _ -> (Op sym (Var x) (Var y))
	  _ -> (Op sym (Var x) (Var y))
	
str_to_lst :: Stmt String -> [Stmt String]
str_to_lst stmt =
  case stmt of
    (Op "." x y) -> (str_to_lst x) ++ (str_to_lst y)
    Var x -> [Var x]
    Free y -> [Free y]
    other -> [other]
    
lst_to_stmt :: [Stmt String] -> Stmt String
lst_to_stmt x = 
  case x of
    [x1] -> x1
    (x1:xs) -> (Op "." x1 (lst_to_stmt xs))

string_order :: Stmt String -> Stmt String
string_order stmt = 
  case stmt of 
    (Op "." _ _) -> lst_to_stmt $ str_to_lst stmt
    x -> x

collapse_funcs :: Stmt String -> [Stmt String]
collapse_funcs stmt =
	case stmt of
		(Var x) -> [stmt]
		(Free x) -> [stmt]
		(Op op (Var x) (Var "NOP")) -> case op of
		  "-" -> [(Var $ "-"++x)]
		  _ -> [stmt]
		(Op op (Var x) (Var y)) -> case op of
			"+" -> [(math (+) "+" x y)]
			"-" -> [(math (-) "-" x y)]
			"*" -> [(math (*) "*" x y)]
			"." -> [string_order stmt]
			_ -> [stmt]
		(Op "." x y) -> [string_order stmt]
		(Op op lhs rhs) -> nub $ 
		                          [(Op op x y) | x <- (collapse_funcs lhs), y <- (collapse_funcs rhs)] ++
		                          [(Op op x rhs) | x <- (collapse_funcs lhs)] ++
		                          [(Op op lhs y) | y <- (collapse_funcs rhs)] ++ [stmt]

		  
f2_expr :: Expr String -> [Expr String]
f2_expr expr =
  let once = f_expr expr in
  concat [f_expr x | x <- once]
		  
f_expr :: Expr String -> [Expr String]
f_expr expr =
	let stmt = (body expr) in
  [Expr (_id expr) x (justification expr) | x <- (collapse_funcs stmt)]

f_exprs :: [Expr String] -> [Expr String]
f_exprs exprs = --exprs
	foldr (++) [] [ f_expr x | x <- exprs ]