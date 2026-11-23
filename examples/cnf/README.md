Base semantics/checker for CNF and supporting extensions

[array](array):
Refinement of generic CNF functions to use arrays

[basis_ffi.c](basis_ffi.c):
A trimmed version of the original CakeML basis_ffi.c, customized for checkers.

[ccnfScript.sml](ccnfScript.sml):
A concrete CNF representation as lists of integers that will be packed.

[cnfScript.sml](cnfScript.sml):
Syntax and semantics of CNF

[dimacsScript.sml](dimacsScript.sml):
Syntax and semantics of CNF in the DIMACS format

[dist](dist):
An distributed RUP checker

[input_lexScript.sml](input_lexScript.sml):
The lexer for the text input formats and the DIMACS skeleton shared by
the CNF formats, followed by scan_toks, which computes the lexer's result
directly on a line.

[lrup](lrup):
An LRUP checker for compressed (variable-byte encoded) proofs

[lsr](lsr):
An LSR checker for compressed (variable-byte encoded) proofs

[syntax_helperScript.sml](syntax_helperScript.sml):
Syntactic print/parse helper files

[xlrup](xlrup):
An XLRUP checker, i.e., LRUP extended with XOR reasoning
