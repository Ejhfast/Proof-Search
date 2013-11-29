module Main where
import Control.Monad
import Control.Monad.Instances
import Data.Char
import Data.List
import Data.Maybe
import Debug.Trace
import ProofFuncs
import ProofParse
import ProofSearch
import ProofTypes
import System.Environment
import System.IO.Unsafe
import System.Timeout as S
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Expr
import Text.Printf
import Text.Show

iter :: Int ->
    [Ruleset String] ->
      [Ruleset String] -> [Expr String] -> [Expr String] -> IO String

iter 0 _ _ _ _ = return "Failed to prove."
iter depth rsets fsets assumps conc =
  let back = (++) conc $
             back_apply_rulesets_stmts conc fsets in
  -- Look backward once with frees
  let expand_back = (++) back $
                    back_apply_rulesets_stmts back rsets in
  -- Generate one layer back from conclusion
  let fwrd = (++) assumps $
             apply_rulesets_stmts assumps fsets in
  -- Look forward with frees
  let expand_fwrd = (++) fwrd $
                    apply_rulesets_stmts fwrd rsets in
  -- Generate one layer forward from assumptions
  let matches = [
        (x , y) |
        x <- expand_fwrd,
        y <- expand_back,
        ProofTypes.body x == ProofTypes.body y]
  in
   case matches of
     (x : rst)
       -> return "Proved"
     _ -> iter (depth - 1) rsets fsets fwrd back

verify :: Int -> [Expr String] -> [Ruleset String] -> [Expr String] -> IO String
verify depth stmt rulesets assumps =
  iter depth rulesets [] assumps stmt

runTest = return verify 4
makeRuleset = parse (parse_rulesets []) ""
makeRulesets = parse (parse_rulesets []) ""
makeAssumptions = parse (parse_assumptions []) ""
makeConc = oparse (parse_conclusion []) ""

-- Test for empty string as input, otherwise parse
maybeParse :: Parser [a] -> String -> Maybe [a]
maybeParse parser str =
  if str == "" then Just [] else
    let tryit = parse parser "" str in
    case tryit of
      (Right res) -> Just res
      _ -> Nothing

main :: IO ()
main = io (map processIt)
io f = interact (unlines . f . lines)

processIt s = show (
  parse (
     parse_assumptions []
     ) "" s
  )

exRule = "\\rewrite{X}{a.a.(\\star{a}+a).b.(\\star{b}+c).b}"
exRuleset = "myfule{"
             ++ exRule ++
             ";"
             ++ exRule ++
             ";"
             ++ exRule ++
             "}"

exRuleset2 = "Test{X+Y~>Y+X;X+Y:=Y+X;}"
testParse = parse (parse_rule mytex) "" ex_rule
testRuleset = parse (parse_ruleset mytex) "" ex_ruleset2
testRulesets = parse (parse_rulesets mytex) "" $ ex_ruleset
                ++ ex_ruleset ++ ex_ruleset
condRuleset = "TestRule{(X+Y+Z~>Z+X+Y)_[Z::(Z=1);Y::(!T)];}"
testCond = parse (parse_ruleset mytex) "" cond_ruleset
