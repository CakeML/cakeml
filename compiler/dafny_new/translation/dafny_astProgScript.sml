(*
 Translates Dafny's AST types.
*)

open preamble
open ml_translatorLib
open cakeml_astProgTheory
open dafny_astTheory

val _ = new_theory "dafny_astProg";

val _ = translation_extends "cakeml_astProg";

val _ = register_type “:program”;

val _ = export_theory ();
