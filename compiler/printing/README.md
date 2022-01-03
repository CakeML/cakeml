The printer mechanism for the CakeML REPL.

CakeML interactive mode (the Read-Eval-Print-Loop or REPL) involves printer
code being added to the target program prior to regular compilation.

Printing code is added in two unverified passes.

Before type checking, each datatype declaration has an implicit pretty-print
function defined, e.g. "pp_box" for a type named "box". These functions may be
shadowed in the usual way, which a user may want to do, to set a custom
printing function.

After type checking, each global declaration which binds a name
(e.g. "val x = f 1") is elaborated to print the result
(e.g. print "val x = 2").

Both passes depend on the standard library providing the necessary functions,
and both passes only activate after those functions appear in the source AST.




[addTypePPScript.sml](addTypePPScript.sml):
The first pass of adding print functions to source AST.
Runs prior to type inference, and defines a pretty-print
function per datatype definition.

[test](test):
This directory contains tests that run the pretty-printer passes inside the HOL
logic and check the type correctness of the resulting code.
