(*
 * Translates definitions to convert Dafny's AST into CakeML's AST.
 *)

open preamble ml_translatorLib
open sexp_to_dafnyProgTheory

val _ = new_theory "dafny_to_cakemlProg";

val _ = translation_extends "sexp_to_dafnyProg";

val r = translate dafny_to_cakemlTheory.from_string_def;
val r = translate dafny_to_cakemlTheory.gen_literal_def;
val r = translate dafny_to_cakemlTheory.gen_expression_def;
val r = translate dafny_to_cakemlTheory.gen_statement_def;
val r = translate dafny_to_cakemlTheory.compile_def;
val r = translate dafny_to_cakemlTheory.unpack_def;

val _ = export_theory ();
