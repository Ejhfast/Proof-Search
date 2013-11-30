-- import HUnit
import Test.HUnit
import ProofFuncs
import ProofParse
import ProofSearch
import ProofTypes
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Expr
import ProofTypes as PT

-------------------------------------------
maybeParse :: Parser [a]
               -> String
               -> Maybe [a]
maybeParse parser str =
  if str == "" then Just [] else
    let tryit = parse parser "" str in
    case tryit of
      (Right res) -> Just res
      _ -> Nothing

-- here we define a set of symbols 
texSymbols = [
  ( "go", 2 ),
  ( "rewrite", 2 ) ,
  ("star" , 1) ,
  ("e" , 0)
  ]


-----------------------------------------
-- 1 rulesets <- look "rulesets"
-- 2 frees <- look "frees"
-- 3 assumptions <- look "assumptions"
-- 4 conclusion <- look "conclusion"
-- 5 syntax <- look "syntax" ( an array of tokens)
-------------------------------------------
iter :: Int -> [Ruleset String] ->
        [Ruleset String] ->
        [Expr String] ->
        [Expr String] -> String
iter 0 _ _ _ _ = "Failed to prove."
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
     (x : rst) ->  "Proved"
     _ -> iter (depth - 1) rsets fsets fwrd back

-------------------------------------------
doProof :: String ->
           String ->
           String ->
           String ->
           String ->
           String
doProof     rulesets frees   assumptions  conclusion  syntax = do
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
                  foo <- iter 2 r f a c
                  return foo
                _ -> "Failure: Error parsing conclusion"
            _ -> "Failure: Error parsing assumptions"
        _ -> "Failure: Error parsing free rulesets"
    _ -> "Failure: Error parsing required rulesets"

-------------------------------------------
runAssign :: String ->
             String ->
             String ->
             String ->
             -- return
             String 
runAssign  rulesets
           assumptions
           goal
           syntax
  = do
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
      "Success: Parsed assignment."
    (p1,
     p2,
     p3) ->
      "Failure: bad parse in assumptions/rulesets." ++
      show p1
      ++ show p2 ++
      show p3
      
-------------------------------------------

testRuleset = parse (parseRuleset [
                        ( "go", 2 ),
                        ( "rewrite", 2 ) ,
                        ("star" , 1) ,
                        ("e" , 0)
                        ]
                    ) "" "Test{X+Y~>Y+X;X+Y:=Y+X;}"

testParseRuleset = parseRuleset [
                        ( "go", 2 ),
                        ( "rewrite", 2 ) ,
                        ("star" , 1) ,
                        ("e" , 0)
                        ]


--parseAssumptions
--test1 = TestCase (assertEqual "blag" testRuleset 1 )

test1 = TestCase (assertEqual "blag" 1 1 )
test2 = TestCase (assertEqual "second test" 3 2)
tests = TestList [TestLabel "test1" test1, TestLabel "test2" test2]

example = "a:1;"

-- Regular Expressions II
-- Unfold : \star{A} = (A. \star{A}) + \e
-- Right Identity : A.\e := A
-- Left Identity :  \e.A = A
-- Absorption : A + \E = \E
-- Select : Replace A+B with A or with B

-- Given : (a + b).\star{a}.\star{b}.a.b
-- (a + b).\star{a}.\star{b}.a.b">(a + b).\star{a}.\star{b}.a.b
-- Text.Parsec.Prim.ParsecT String () Data.Functor.Identity.Identity (Ruleset String)

fakeParse :: Parser (Stmt String)
fakeParse = do {
  x <- string "0";
  return (Var x)
  }



  -- argParse
  -- carrot
  -- constraint
  -- constraints
            
  -- parseTexCommand, called by createCommands
  -- createCommands called by allFuncs
  -- allFuncs called by recurse
            
  -- factor
  -- modifiers
  -- number
  -- parseAssumption
  -- parseAssumptions
  -- parseConclusion
  -- parseRule
  -- parseRuleset

  -- recurse called by parseAssumption, and parseRule, symbol
  -- symbol
  -- tryall
  -- underscore

derive        = parse (     parseRule []     ) "" "X+Y~>Y+X"
derive_x = Right (
  Rule {
     condition = Op "+"
                 (Free "X")
                 (Free "Y"),
     conclusion = Op "+"
                  (Free "Y")
                  (Free "X"),
     kind = Equality,
     cnst = []
     }
  )

commutativity = parse (     parseRule []     ) "" "X+Y:=Y+X;"
commutativity_x = Right (
  Rule {
     condition = Op "+"
                 (Free "X")
                 (Free "Y"),
     conclusion = Op "+"
                  (Free "Y")
                  (Free "X"),
     kind = Strict,
     cnst = []})

unfold        = parse (     parseRule texSymbols     ) "" "\\star{A} := (A. \\star{A}) + e "  
right_identity= parse (     parseRule []     ) "" "A.e := A"  
left_identity = parse (     parseRule []     ) "" "e.A := A"  
absorption    = parse (     parseRule []     ) "" "A + e := e"  
selecta       = parse (     parseRule []     ) "" "A + B := B"  
selectb       = parse (     parseRule []     ) ""  "A + B := A"  
-- absorption: 
-- Right (Rule {condition = Var "NOP", conclusion = Var "NOP", kind = Strict, cnst = []})
-- selecta: 
-- Right (Rule {condition = Var "NOP", conclusion = Var "NOP", kind = Strict, cnst = []})
-- selectb: 
-- Right (Rule {condition = Var "NOP", conclusion = Var "NOP", kind = Strict, cnst = []})



--parse_tex_star  = parse ( parseTexCommand texSymbols) ""  "\\star" 2 
example_ruleset = parse (parseRulesets texSymbols)
                 "" "Test{A=B;C=D;}"
                  


main2 = do
  putStrLn ("parseAssumptions: "  );
  putStrLn (show (  parse (     parseAssumptions []     ) "" "a:1;"  ));

  putStrLn ("commutativity: "  );
  putStrLn (show ( commutativity));
    
  putStrLn ("derive: "  );
  putStrLn (show ( derive ));
  
  putStrLn ("unfold: "  );
  putStrLn (show ( unfold        ));
  putStrLn ("right_identity: "  );
  putStrLn (show ( right_identity ));
  putStrLn ("left_identity: "  );
  putStrLn (show ( left_identity ));
  putStrLn ("absorption: "  );
  putStrLn (show ( absorption    ));
  putStrLn ("selecta: "  );
  putStrLn (show ( selecta      ));
  putStrLn ("selectb: "  );
  putStrLn (show ( selectb      ));
  

--  putStrLn ("parse tex star: "  );
--  putStrLn (show (   parse_tex_star      ));

  putStrLn ("example ruleset: "  );
  putStrLn(show(example_ruleset));

  
--    putStrLn (show (testParseRuleset));
--      putStrLn (testParseRuleset);
    -- ++  show 
    putStrLn ("this is a test2: " )

main = do runTestTT tests;
            main2
  
-- Show (Parser (Ruleset String))) 
--  (Num (Parser (Ruleset String)))
        
