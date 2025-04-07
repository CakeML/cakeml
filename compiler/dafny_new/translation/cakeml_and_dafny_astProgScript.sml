(*
 Translates CakeML's and Dafny's AST types.
*)

open preamble
open basis
open dafny_astTheory

val _ = new_theory "cakeml_and_dafny_astProg";

val _ = translation_extends "basisProg";

val _ = register_type “:ast$dec”;
val _ = register_type “:dafny_ast$program”;

val _ = export_theory ();
