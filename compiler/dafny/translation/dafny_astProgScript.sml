(*
 * Translates functions for Dafny's AST.
 *)

open preamble ml_translatorLib
open cakeml_and_dafny_astProgTheory
open dafny_astTheory

val _ = new_theory "dafny_astProg";

val _ = translation_extends "cakeml_and_dafny_astProg";

val r = translate dafny_astTheory.dest_Ident_def;
val r = translate dafny_astTheory.dest_varName_def;
val r = translate dafny_astTheory.dest_Method_def;
val r = translate dafny_astTheory.unescape_string_def;

val _ = export_theory ();
