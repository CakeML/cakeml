(*
 Translates Dafny's AST types.
*)
Theory dafny_astProg
Ancestors
  AstSexpProg dafny_ast
Libs
  preamble ml_translatorLib


val _ = translation_extends "AstSexpProg";

val _ = register_type “:program”;
