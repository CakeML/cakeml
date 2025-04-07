(*
 Translates definitions to lex and parse S-expressions generated by Dafny.
*)

open preamble
open ml_translatorLib
open result_monadProgTheory
open dafny_sexpTheory

val _ = new_theory "dafny_sexpProg";

val _ = translation_extends "result_monadProg";

val _ = register_type “:dafny_sexp$token”;
val _ = register_type “:dafny_sexp$sexp”;

val r = translate dafny_sexpTheory.read_quoted_aux_def;
val r = translate dafny_sexpTheory.read_quoted_def;

val r = translate boolTheory.IN_DEF;
val r = translate listTheory.LIST_TO_SET_DEF;
val r = translate dafny_sexpTheory.read_atom_aux_def;

val r = translate dafny_sexpTheory.read_atom_def;
val r = translate dafny_sexpTheory.lex_aux_def;
val r = translate dafny_sexpTheory.lex_def;
val r = translate dafny_sexpTheory.parse_aux_def;
val r = translate dafny_sexpTheory.parse_def;

val _ = export_theory ();
