(*
 Translates definitions to generate Dafny's AST from S-expressions.
*)

open preamble
open ml_translatorLib
open dafny_sexpProgTheory
open sexp_to_dafnyTheory

val _ = new_theory "sexp_to_dafnyProg";

val _ = translation_extends "dafny_sexpProg";

val r = translate sexp_to_dafnyTheory.to_mlstring_def;
val r = translate sexp_to_dafnyTheory.to_bool_def;
val r = translate sexp_to_dafnyTheory.to_int_def;
val r = translate sexp_to_dafnyTheory.dest_expr_def;
val r = translate sexp_to_dafnyTheory.split_def;

val r = translate sexp_to_dafnyTheory.dest_fail_def;
val r = translate sexp_to_dafnyTheory.dest0_def;

val r = translate listTheory.list_case_def;
val r = translate sexp_to_dafnyTheory.dest1_def;

val r = translate sexp_to_dafnyTheory.dest2_def;
val r = translate sexp_to_dafnyTheory.dest3_def;
val r = translate sexp_to_dafnyTheory.dest5_def;
val r = translate sexp_to_dafnyTheory.dest7_def;
val r = translate sexp_to_dafnyTheory.dest9_def;

val r = translate sexp_to_dafnyTheory.bad_con_def;
val r = translate sexp_to_dafnyTheory.to_type_def;
val r = translate sexp_to_dafnyTheory.to_mlstring_type_tup_def;
val r = translate sexp_to_dafnyTheory.to_mlstring_type_tup_lst_def;
val r = translate sexp_to_dafnyTheory.to_un_op_def;
val r = translate sexp_to_dafnyTheory.to_bin_op_def;
val r = translate sexp_to_dafnyTheory.to_lit_def;

val r = translate sexp_to_dafnyTheory.to_exp_def;

val r = translate sexp_to_dafnyTheory.to_exp_list_def;
val r = translate sexp_to_dafnyTheory.to_exp_type_tup_def;
val r = translate sexp_to_dafnyTheory.to_exp_type_tup_lst_def;
val r = translate sexp_to_dafnyTheory.to_lhs_exp_def;
val r = translate sexp_to_dafnyTheory.to_lhs_exp_list_def;
val r = translate sexp_to_dafnyTheory.to_rhs_exp_def;
val r = translate sexp_to_dafnyTheory.to_lhs_rhs_exp_tup_def;
val r = translate sexp_to_dafnyTheory.to_lhs_rhs_exp_tup_list_def;

val r = translate sexp_to_dafnyTheory.to_statement_def;
val r = translate sexp_to_dafnyTheory.to_member_decl_def;
val r = translate sexp_to_dafnyTheory.to_program_def;

val _ = export_theory ();
