(*
  Translates transformations on Dafny's AST.
*)

open preamble
open ml_translatorLib
open dafny_to_cakemlProgTheory
open dafny_transformTheory

val _ = new_theory "dafny_transformProg";

val _ = translation_extends "dafny_to_cakemlProg";

val r = translate dafny_transformTheory.rename_var_exp_def;
val r = translate dafny_transformTheory.rename_vars_exp_def;
val r = translate dafny_transformTheory.rename_var_lhs_def;
val r = translate dafny_transformTheory.rename_var_rhs_def;
val r = translate dafny_transformTheory.rename_var_stmt_def;
val r = translate dafny_transformTheory.rename_vars_stmt_def;
val r = translate dafny_transformTheory.fresh_vname_def;
val r = translate dafny_transformTheory.fresh_exp_def;
val r = translate dafny_transformTheory.fresh_lhs_exp_def;
val r = translate dafny_transformTheory.map_fresh_lhs_exp_def;
val r = translate dafny_transformTheory.fresh_rhs_exp_def;
val r = translate dafny_transformTheory.map_fresh_rhs_exp_def;
val r = translate dafny_transformTheory.rename_locals_def;
val r = translate dafny_transformTheory.fresh_stmt_def;
val r = translate dafny_transformTheory.fresh_member_def;
val r = translate dafny_transformTheory.use_fresh_vars_def;

val _ = export_theory ();
