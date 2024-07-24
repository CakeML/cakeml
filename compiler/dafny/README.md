Translate Dafny into CakeML.

[compilation](compilation):
Compilation scripts for the Dafny to CakeML backend.

[dafny_astScript.sml](dafny_astScript.sml):
Definition of Dafny abstract syntax (AST).

[dafny_compilerScript.sml](dafny_compilerScript.sml):
* Definition of the Dafny to CakeML compiler.

[dafny_sexpScript.sml](dafny_sexpScript.sml):
* Definitions to lex and parse S-expressions.

[dafny_to_cakemlScript.sml](dafny_to_cakemlScript.sml):
Definitions to convert Dafny's AST into CakeML's AST.

[result_monadScript.sml](result_monadScript.sml):
* Definition of a specialized Either monad, where an error is a string.

[sexp_to_dafnyScript.sml](sexp_to_dafnyScript.sml):
Definition of functions to generate Dafny's abstract syntax tree.

[translation](translation):
Translation scripts for the Dafny compiler.
