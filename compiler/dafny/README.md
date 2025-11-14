A verified VCG and verified compiler for Dafny

[compilation](compilation):
Compilation scripts for the Dafny to CakeML backend.

[dafny_astScript.sml](dafny_astScript.sml):
Abstract Syntax Tree for a subset of Dafny.

[dafny_compilerScript.sml](dafny_compilerScript.sml):
Definition of the Dafny to CakeML compiler.

[dafny_freshenScript.sml](dafny_freshenScript.sml):
Implements the freshen pass, where names are updated to be unique.

[dafny_sexpScript.sml](dafny_sexpScript.sml):
Definitions to lex and parse S-expressions.

[dafny_to_cakemlScript.sml](dafny_to_cakemlScript.sml):
Defines the translation of Dafny's to CakeML's AST.

[examples](examples):
Contains programs to test the verified Dafny compiler.

[proofs](proofs):
Correctness proofs for the Dafny compiler.

[result_monadScript.sml](result_monadScript.sml):
Definition of a specialized Either monad, where an error is an mlstring.

[semantics](semantics):
Definition of Dafny's semantics.

[sexp_to_dafnyScript.sml](sexp_to_dafnyScript.sml):
Parses an S-expression into a Dafny AST.

[translation](translation):
Translation scripts for the Dafny compiler.

[vcg](vcg):
Verification condition generation (VCG) for Dafny.
