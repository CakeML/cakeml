(*
 Translates CakeML's AST types, extending basisProg.
*)
Theory cakeml_astProg
Ancestors
  basisProg
Libs
  preamble basis


val _ = translation_extends "basisProg";

val _ = register_type “:dec”;
