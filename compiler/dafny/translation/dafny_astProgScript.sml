(*
 Translates Dafny's AST types.
*)
Theory dafny_astProg
Ancestors
  cakeml_astProg dafny_ast
Libs
  preamble ml_translatorLib


val _ = translation_extends "cakeml_astProg";

val _ = register_type “:program”;

