A PEG-based parser for a subset of the OCaml language, for use with the Candle
theorem prover.

[camlCompileScript.sml](camlCompileScript.sml):
Compiles the OCaml parser things.

[camlPEGScript.sml](camlPEGScript.sml):
Definition of a PEG for (a subset of) OCaml.

[camlProgScript.sml](camlProgScript.sml):
I/O wrapper for the OCaml parser.

[camlPtreeConversionScript.sml](camlPtreeConversionScript.sml):
A theory for converting OCaml parse trees to abstract syntax.

[caml_lexProgScript.sml](caml_lexProgScript.sml):
Translation of the functions and types in caml_lexScript.sml

[caml_lexScript.sml](caml_lexScript.sml):
Lexer for the OCaml frontend.

[caml_parserProgScript.sml](caml_parserProgScript.sml):
Translation of the functions in caml_parserScript.sml

[caml_parserScript.sml](caml_parserScript.sml):
Parser entry-point for the OCaml parser.

[caml_ptreeProgScript.sml](caml_ptreeProgScript.sml):
Translation of the functions in camlPEGScript.sml and
camlPtreeConversionScript.sm

[caml_sexprScript.sml](caml_sexprScript.sml):
Generates an s-expression from the OCaml parser things that
can be fed into the CakeML compiler binary.

[sexp_parserProgScript.sml](sexp_parserProgScript.sml):
Translate the alternative s-expression parser.
