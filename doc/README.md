# Documentation

The executable reads source code from stdin and outputs llvm code through stdout.
Error reporting, which can only occour during type checking, is writen to stderr. 


## The javalette language
The grammer is specified in src/javalette.cf.
We refer to src/WellTyped.agda as a reference on well typed expressions and statments.

## shift/reduce conflicts
The parsers has one shift conflicts: dangling else.
Which is a common shift/reduce conflict.
This is caused by our cond and cond-else statements, since it does not know whether or not the conditional statement is followed by an else. 

Concrelty, 

if (a) if b s; else s2;

Can be parsed in two ways

if (a) (if (b) s;) else s2;
if (a) (if (b) s;  else s2;)

Our parses chooses the latter.


## Extensions

arrays1, arrays2 and pointers