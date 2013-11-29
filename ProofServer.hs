module Main where
import Control.Monad (msum)
import Happstack.Server
import System.Environment
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Data.List
import Debug.Trace
import System.Timeout as S
import ProofParse
import ProofTypes as PT
import ProofFuncs
import ProofSearch
import System.IO.Unsafe

runConfOld port = Conf port Nothing (logAccess nullConf) 5
--- port Nothing (logAccess nullConf) 5
runConf port_n =  Conf
                      { 
                        port      = port_n,
                        validator = Nothing,
                        logAccess = Just logMAccess,
--                        threadGroup = 
                        Happstack.Server.timeout   = 30
                      }
                      
main :: IO ()
main = do
  args <- getArgs
  let port = read (head args) :: Int
  simpleHTTP (runConf port)  app

app :: ServerPart Response
app = do
  decodeBody (defaultBodyPolicy "/tmp/" 0 10000 10000)
  msum [ dir "check_proof" checkProof,
         dir "check_assignment" checkAssign,
         dir "health" health ]

-- This is so S3 can test whether a server is responding
health :: ServerPart Response
health = do
 methodM GET
 ok $ toResponse "Healthy"

checkProof :: ServerPart Response
checkProof = do
  methodM POST
  rulesets <- look "rulesets"
  frees <- look "frees"
  assumptions <- look "assumptions"
  conclusion <- look "conclusion"
  syntax <- look "syntax"
  let new_parse_funcs =
        if syntax == ""
        then []
        else read syntax :: [(String, Int)]
  let try_rulesets =
        maybeParse (parseRulesets new_parse_funcs)
        $ removeWs rulesets
  case try_rulesets of
    Just r ->
      let try_frees = maybeParse
                      (parseRulesets new_parse_funcs) $
                      removeWs frees in
      case try_frees of
        Just f ->
          let try_assumps =
                maybeParse
                (parseAssumptions new_parse_funcs) $
                removeWs assumptions in
          case try_assumps of
            Just a ->
              let try_conc =
                    maybeParse (parseConclusion
                                new_parse_funcs)
                    $ removeWs conclusion in
              case try_conc of
                Just c -> do
                  res <- iter 2 r f a c
                  ok $ toResponse res
                _ -> ok $ toResponse "Failure: Error parsing conclusion"
            _ -> ok $ toResponse "Failure: Error parsing assumptions"
        _ -> ok $ toResponse "Failure: Error parsing free rulesets"
    _ -> ok $ toResponse "Failure: Error parsing required rulesets"

checkAssign :: ServerPart Response
checkAssign = do
  methodM POST
  rulesets <- look "rulesets"
  assumptions <- look "assumptions"
  goal <- look "goal"
  syntax <- look "syntax"
  let new_parse_funcs =
        if syntax == ""
        then []
        else read syntax :: [(String, Int)]
  let rs_parsed = parse (parseRulesets new_parse_funcs)
                  "" $ removeWs rulesets
  let as_parsed = parse (parseAssumptions new_parse_funcs)
                  "" $ removeWs assumptions
  let g_parsed = parse (recurse "ground" new_parse_funcs)
                 "" $ removeWs goal
  case (rs_parsed, as_parsed, g_parsed) of
    (Right r, Right a, Right go) ->
      ok $
      toResponse "Success: Parsed assignment."
    (p1,
     p2,
     p3) ->
      ok $ toResponse $
      "Failure: bad parse in assumptions/rulesets." ++
      show p1
      ++ show p2 ++
      show p3


aps a s =
  case
    unsafePerformIO $ S.timeout 500000 $
    return $
    applyRulesetsStmts a s
  of
    Just x -> x
    _ -> []

baps a s =
  case
    unsafePerformIO $ S.timeout 500000 (
      return $ backApplyRulesetsStmts a s
      )
  of
    Just x -> x
    _ -> []

iter :: Int -> [Ruleset String] ->
        [Ruleset String] ->
        [Expr String] ->
        [Expr String] -> ServerPartT IO String
iter 0 _ _ _ _ = return "Failed to prove."
iter depth rsets fsets assumps conc =
  let back = (++) conc $
             backApplyRulesetsStmts
             conc fsets in -- Look backward once with frees
  let expand_back = (++)
                    back $
                    backApplyRulesetsStmts
                    back rsets in -- Generate one layer back from conclusion
  let fwrd = (++)
             assumps $
             applyRulesetsStmts assumps fsets in -- Look forward with frees
  let expand_fwrd = (++)
                    fwrd $ applyRulesetsStmts fwrd rsets
  in -- Generate one layer forward from assumptions
   let matches = [(x , y) |
                  x <- expand_fwrd,
                  y <- expand_back,
                  PT.body x == PT.body y] in
   case matches of
     (x : rst) -> return "Proved"
     _ -> iter (depth - 1) rsets fsets fwrd back

-- Test for empty string as input, otherwise parse
maybeParse :: Parser [a]
               -> String
               -> Maybe [a]
maybeParse parser str =
  if str == "" then Just [] else
    let tryit = parse parser "" str in
    case tryit of
      (Right res) -> Just res
      _ -> Nothing
