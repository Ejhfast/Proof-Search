-- import HUnit
import Test.HUnit
import ProofFuncs
import ProofParse
import ProofSearch
import ProofTypes
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Expr

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

  -- allFuncs
  -- argParse
  -- carrot
  -- constraint
  -- constraints
  -- createCommands
  -- factor
  -- modifiers
  -- number
  -- parseAssumption
  -- parseAssumptions
  -- parseConclusion
  -- parseRule
  -- parseRuleset
  -- parseTexCommand
  -- recurse
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

unfold        = parse (     parseRule []     ) "" "star{A} := (A. star{A}) + e "  
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


tex_star = '\\star'

main2 = do
  putStrLn ("this is a test: "  );
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
  

  
--    putStrLn (show (testParseRuleset));
--      putStrLn (testParseRuleset);
    -- ++  show 
    putStrLn ("this is a test2: " )

main = do runTestTT tests;
            main2
  
-- Show (Parser (Ruleset String))) 
--  (Num (Parser (Ruleset String)))
        
