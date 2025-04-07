(*
 Translates definitions to generate Dafny's AST from S-expressions.
*)

open preamble
open ml_translatorLib
open dafny_sexpProgTheory
open sexp_to_dafnyTheory

val _ = new_theory "sexp_to_dafnyProg";

val _ = translation_extends "dafny_sexpProg";

val r = translate sexp_to_dafnyTheory.to_string_def;
val r = translate sexp_to_dafnyTheory.to_bool_def;
val r = translate sexp_to_dafnyTheory.to_int_def;
val r = translate sexp_to_dafnyTheory.dest_expr_def;
val r = translate sexp_to_dafnyTheory.split_def;
val r = translate sexp_to_dafnyTheory.dest0_def;

val r = translate listTheory.list_case_def;
val r = translate sexp_to_dafnyTheory.dest1_def;

val r = translate sexp_to_dafnyTheory.dest2_def;
val r = translate sexp_to_dafnyTheory.dest3_def;
val r = translate sexp_to_dafnyTheory.dest5_def;
val r = translate sexp_to_dafnyTheory.dest6_def;
val r = translate sexp_to_dafnyTheory.dest9_def;

val r = translate sexp_to_dafnyTheory.extend_path_def;
val r = translate sexp_to_dafnyTheory.to_type_def;
val r = translate sexp_to_dafnyTheory.to_string_type_tup_def;
val r = translate sexp_to_dafnyTheory.to_string_type_tup_lst_def;
val r = translate sexp_to_dafnyTheory.to_bop_def;
val r = translate sexp_to_dafnyTheory.to_literal_def;

val r = translate sexp_to_dafnyTheory.to_expression_def;

val r = translate sexp_to_dafnyTheory.to_expression_list_def;
val r = translate sexp_to_dafnyTheory.to_assign_rhs_def;
val r = translate sexp_to_dafnyTheory.to_assign_rhs_list_def;

val r = translate sexp_to_dafnyTheory.to_statement_def;
val r = translate sexp_to_dafnyTheory.to_member_decl_def;
val r = translate sexp_to_dafnyTheory.to_program_def;

val _ = export_theory ();
