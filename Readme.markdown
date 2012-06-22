# Proof Checking Framework

## General Status 

### (Mostly) Supported So Far:

+ Proof Search: forward and backward
+ Verification: Check if statement is provable (given resources/time)
+ Rule Types: Rewrites, equalities
+ Functions: Support for basic mathematical operations
+ Strings: For constructing CFGs
+ Parsing: Now handled on the backend with Parsec
+ Web API for all of above


### Directory Structure

+ proofserver.hs  :  web-server and API for backend interface
+ proofsearch.hs  :  code for search
+ prooftypes.hs   :  define types on Expressions and Rules for easy destructuring
+ prooffuncs.hs   :  apply and collapse functions on Expression objects
+ proofparse.hs   :  parse input strings into internal representation
+ prooftest.hs    :  a few test cases

### License

Copyright (C) 2012 Ethan Fast

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.