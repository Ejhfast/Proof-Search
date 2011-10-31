## Proof Checking Framework

### General Status 

#### (Mostly) Supported So Far:

+ Proof Search: forward and backward
+ Verification: Check if statement is provable (given resources/time)
+ Rule Types: Strict rewrites, equalities, and generative
+ Functions: Support for basic mathematical operations
+ Strings: For constructing CFGs
+ Parsing: Now handled on the backend with Parsec
+ Deparsing: Built into Stmt types
+ Web interface for all of above

#### Working on:

+ Better error messages
+ More efficient search

#### Directory Structure

+ proofserver.hs  :  web-server and API for backend interface
+ proofsearch.hs  :  code for search
+ prooftypes.hs   :  define types on Expressions and Rules for easy destructuring
+ prooffuncs.hs   :  apply and collapse functions on Expression objects
+ proofparse.hs   :  parse input strings into internal representation
+ prooftest.hs    :  a few test cases

### A few examples

#### Rulesets

##### Rewrite Rules

Strict rewrite rules are (currently) represented with '~>' and will not be applied within sub-expressions. For instance: 

+ The rule A&B~>A can be applied to the expression "A&B" but not "A&B=>C"

However, they remain general in the sense that more complex terms will still find mappings. E.g:

+ The statement ~A&~(B|R) will map ~A to A and ~(B|R) to B and produce ~A

##### Equalities

Equality rules are (currently) represented with '-->' and will be applied to sub-expressions. Replacements will therefore be made without reference to context. E.g.

+ The rule ~(A|B)-->~A&~B can be applied to B=>~(C|F) to produce B=>~C&~F

Despite the fact that these rules search through sub-expressions, in practice they do not seem of far higher cost than strict rewrites.

##### Generative Rules

Generative rules state a conclusion only, and dictate how expressions may be legally combined. They are expressed of the form #(expr), where expr presents an allowed combination. For instance, suppose that we know P, and that we also know Q. We may want the system to be prove "P and Q" or rather propositionally: P,Q. The rule for this is:

+ #(A,B)

Here A and B represent arbitrary expressions, and will therefore match anything. This rule says that if we know anything, and we also know anything else, then we may state "the first anything comma the anything else." If we want to constrain one or more of these terms, we need additional syntax. For instance:

+ #(A,B<-(C=>D))

Through B<-(C=>D) this rule says that B must be of the general form C=>D, and so we are allowed to state "anything comma any implication".