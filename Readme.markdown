### Framework for constructing rewrite rules. 

#### (Mostly) Supported So Far:

+ Proof Search: forward and backward
+ Verification: Check if statement is provable (given resources/time)
+ Rule Types: Strict rewrites, equalities, and unconditional statements
+ Functions: Support for basic mathematical operations
+ Strings: For constructing CFGs
+ Parsing: Now handled on the backend with Parsec
+ Deparsing: Built into Stmt types
+ Web interface for all of above

#### Working on:

+ Better error messages
+ More efficient search
+ Clean up parsing system

#### Directory Structure

+ proofserver.hs  :  web-server defining an API for backend interface
+ proofsearch.hs  :  code for search
+ prooftypes.hs   :  define types on Expressions and Rules for easy destructuring
+ prooffuncs.hs   :  apply and collapse functions on Expression objects
+ proofparse.hs   :  parse input strings into internal representation
+ prooftest.hs    :  a few test cases
