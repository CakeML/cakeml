(*
 Translates Dafny's AST types.
*)
Theory dafny_astProg
Ancestors
  basisProg dafny_ast
Libs
  preamble ml_translatorLib


val _ = translation_extends "basisProg";

val _ = register_type “:program”;
