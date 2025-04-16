Translate Dafny into CakeML using a custom intermediate representation.

[dafny_astScript.sml](dafny_astScript.sml):
Abstract Syntax Tree for a subset of Dafny.

[dafny_sexpScript.sml](dafny_sexpScript.sml):
Definitions to lex and parse S-expressions.

[dafny_to_cakemlScript.sml](dafny_to_cakemlScript.sml):
Defines the translation of Dafny's to CakeML's AST.

[result_monadScript.sml](result_monadScript.sml):
Definition of a specialized Either monad, where an error is an mlstring.

[semantics](semantics):
Definition of Dafny's semantics.

[sexp_to_dafnyScript.sml](sexp_to_dafnyScript.sml):
Parses an S-expression into a Dafny AST.

[tests](tests):
Contains programs to test the Dafny compiler.

[translation](translation):
Translation scripts for the Dafny compiler.
