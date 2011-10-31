# Proof Checking Framework

## General Status 

### (Mostly) Supported So Far:

+ Proof Search: forward and backward
+ Verification: Check if statement is provable (given resources/time)
+ Rule Types: Strict rewrites, equalities, and generative
+ Functions: Support for basic mathematical operations
+ Strings: For constructing CFGs
+ Parsing: Now handled on the backend with Parsec
+ Deparsing: Built into Stmt types
+ Web interface for all of above

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

Rulesets are groups of rules that share a common name and description. Usually, the rules within a ruleset represent different ways of producing the "same" sort of transformation. A ruleset is defined as:

	RulesetName{
	  "Description of ruleset"
	  Rule1;
	  Rule2;
	  ...
	  RuleN;	
	}

Where each Rule(i) is either a rewrite, equality, or generative rule.

#### Rewrite Rules

Strict rewrite rules are (currently) represented with ~> and will not be applied 
within sub-expressions. For instance: 

	The rule A&B~>A can be applied to the expression "A&B" but not "A&B=>C"

However, they remain general in the sense that more complex terms will still find 
mappings. E.g:

	The statement ~A&~(B|R) will map ~A to A and ~(B|R) to B and produce ~A

#### Equalities

Equality rules are (currently) represented with --> and will be applied to sub-
expressions. Replacements will therefore be made without reference to context. E.g.

	The rule ~(A|B)-->~A&~B can be applied to B=>~(C|F) to produce B=>~C&~F

Despite the fact that these rules search through sub-expressions, in practice they
do not seem of far higher cost than strict rewrites.

#### Generative Rules

Generative rules state a conclusion only, and so dictate how expressions may be legally
combined. They are expressed of the form #(expr), where expr presents an allowed 
combination. For instance, suppose that we know P, and that we also know Q. We may want 
the system to be prove "P and Q" or rather propositionally: P,Q. The rule for this is:

	#(A,B)

Here A and B represent arbitrary expressions, and will therefore match anything. This
rule says that if we know anything, and we also know anything else, then we may state
"the first anything comma the anything else." If we want to constrain one or more of 
these terms, we need additional syntax. For instance:

	#(A,B<-(C=>D))

Through B<-(C=>D) this rule says that B must be of the general form C=>D, and so we 
are allowed to state "anything comma any implication".

### Expressions

Expressions are the basic facts of the system. They can be entered in a 'common' infix notation. E.g.

+ A+B
+ 4*X+5*Y
+ A&B|C

Although the underlying proof checking system is completely general, the expression parser is not. At the moment it supports basic mathematical notation (+,-,\*), predicate logic (&,|), and (for CFGs) string concatenation (. <--dot). Where appropriate in expressions, certain functions are allowed to collapse (eventually, these may be user-specified). An example of this is (3\*X+3\*X), which will collapse to 6\*X.

Although rules are written in the form of expressions, the system parses expressions differently. In the rule A&B~>B, A and B are "free" variables which can represent any fact in the system. But for the expression B&C, B and C have single, set values.

#### Example Rulesets and Assumptions

Here are some rulesets put together for the purpose of basic logical proofs.

	Free{
	  ""
	  #(A,B);
	}
	PP{
	  "P => Q & P -> Q"
	  P,(P=>Q)~>Q;
	}
	TT{
	  "P => Q & ~Q -> ~P"
	  (P=>Q)~>(~Q=>~P);
	  ~Q,(P=>Q)~>~P;
	}
	TP{
	  "(P | Q) & ~P -> Q"
	  (P|Q),~P~>Q;
	  (P|Q),~Q~>P;
	  (P|Q)~>(~P=>Q);
	  (P|Q)~>(~Q=>P);
	  ~P~>(P|Q)=>Q;
	}
	DN{
	 "P <-> ~P"
	  P~>(P=>~(~P));
	  ~(~P)~>(~(~P)=>P);
	  P-->~(~P);
	  ~(~P)-->P;
	}
	S{
	  "P & Q -> P, P & Q -> Q"
	  (P&Q)~>P;
	  (P&Q)~>Q;
	  (R=>P&Q)~>R=>P;
	  (R=>P&Q)~>R=>Q;
	  (A,(B&A=>C))~>B=>C;
	  (A,(A&B=>C))~>B=>C;
	  A~>(B=>B&A);
	}
	A{
	  "P -> (Q => P & Q)"
	  P~>(Q=>(P&Q));
	  P~>(Q=>(Q&P));
	}
	HS{
	  "(P => Q) & (Q => R) -> P => R"
	  ((P=>Q),(Q=>R))~>(P=>R);
	}
	LA{
	"P -> P | Q"
	  P~>(P=>(P|Q));
	  P-->(P|Q);
	}
	DM{
	  "~(P & Q) <-> ~P | ~Q, ~(P | Q) <-> ~P & ~Q"
	  (P&Q)-->~(~P|~Q);
	  ~(P&Q)-->~P|~Q;
	  (P|Q)-->~(~P&~Q);
	  ~(P|Q)-->~P&~Q;
	  ~(~P|~Q)-->P&Q;
	  ~P|~Q-->~(P&Q);
	}
	REFL{ 
	  "A => A"
	  A~>(A=>A);
	}
	DP{
	  "P | P -> P"
	  (P|P)-->P;
	}
	DS{
	  "(P => R) & (Q => S) -> (P | Q) => (R | S)"
	  (P=>R),(Q=>S)~>((P|Q)=>(R|S));
	  (P=>R),(Q=>S),(P|Q)~>(R|S);
	}
	CL{
	  "P & Q -> Q & P, P | Q -> Q | P"
	  (P&Q)-->(Q&P);
	  (P|Q)-->(Q|P);
	}
	
Likewise, some example assumptions:

	AS1: R=>N;
	AS2: K=>(B|R);
	AS3: (Q|M)=>K;
	AS4: ~N;