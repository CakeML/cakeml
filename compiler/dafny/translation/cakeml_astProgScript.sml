(*
 Translates CakeML's AST types, extending basisProg.
*)

open preamble
open basis

val _ = new_theory "cakeml_astProg";

val _ = translation_extends "basisProg";

val _ = register_type “:dec”;

val _ = export_theory ();
