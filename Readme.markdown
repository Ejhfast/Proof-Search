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

### Working on:

+ Better error messages
+ More efficient search

### Directory Structure

+ proofserver.hs  :  web-server and API for backend interface
+ proofsearch.hs  :  code for search
+ prooftypes.hs   :  define types on Expressions and Rules for easy destructuring
+ prooffuncs.hs   :  apply and collapse functions on Expression objects
+ proofparse.hs   :  parse input strings into internal representation
+ prooftest.hs    :  a few test cases

## Quick Description

Given a set of rules and a set of expressions, we apply a brute-force combination of forward and backward search to verify statements entered by a user. Search works by producing and generating new expressions, applying rule-based transformations upon what the system already knows.  

### Rulesets

#### Definition

Rulesets are groups of rules that share a common name and description. Usually, the rules within a ruleset represent different ways of producing the "same" sort of transformation. 

#### Rewrite Rules

Rewrite rules are (currently) represented with := and will not be applied 
within sub-expressions. For instance: 

	The rule A&B~>A can be applied to the expression "A&B" but not "A&B=>C"

However, they remain general in the sense that more complex terms will still find 
mappings. E.g:

	Applying the above rule, the statement ~A&~(B|R) will map ~A to A and ~(B|R) to B and produce ~A

#### Equalities

Equality rules are (currently) represented with ~> and will be applied to sub-expressions. 
Replacements will be made without reference to context. E.g.

	The rule ~(A|B)~>~A&~B can be applied to B=>~(C|F) to produce B=>~C&~F

### Expressions

Expressions are the basic facts of the system. They can be entered in a 'common' infix notation. E.g.

+ A+B
+ 4*X+5*Y
+ A&B|C

Although the underlying proof checking system is general, the expression parser is not. It supports basic mathematical notation (+,-,\*,\\), predicate logic (&,|), and (for CFGs) string concatenation (. <--dot). Functions of + and * may collapse (eventually, these may be user-specified). For instance, (3\*X+3\*X) will collapse to 6\*X.

Although rules are written in the form of expressions, the system parses expressions differently. In the rule A&B~>B, A and B are "free" variables which can represent any fact in the system. But for the expression B&C, B and C have single, set values.