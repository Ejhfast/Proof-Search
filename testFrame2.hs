-- import HUnit
import Test.HUnit

test1 = TestCase (assertEqual "blag" 1 1 )
test2 = TestCase (assertEqual "second test" 3 2)
        
tests = TestList [TestLabel "test1" test1, TestLabel "test2" test2]

main = runTestTT tests