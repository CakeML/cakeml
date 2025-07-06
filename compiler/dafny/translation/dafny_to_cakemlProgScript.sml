(*
  Translates definitions to translate from Dafny's to CakeML's AST.
*)

open preamble
open ml_translatorLib
open sexp_to_dafnyProgTheory
open dafny_to_cakemlTheory
open namespaceTheory
open locationTheory

val _ = new_theory "dafny_to_cakemlProg";

val _ = translation_extends "sexp_to_dafnyProg";

val r = translate dafny_to_cakemlTheory.cml_list_def;

val r = translate astTheory.Funs_def;
val r = translate dafny_to_cakemlTheory.cml_new_refs_def;

val r = translate dafny_to_cakemlTheory.cml_fun_def;
val r = translate dafny_to_cakemlTheory.cml_tup_vname_def;
val r = translate dafny_to_cakemlTheory.Stuple_def;
val r = translate dafny_to_cakemlTheory.Pstuple_def;
val r = translate dafny_to_cakemlTheory.cml_tup_case_def;
val r = translate dafny_to_cakemlTheory.cml_tup_select_def;
val r = translate dafny_to_cakemlTheory.cml_alloc_arr_def;
val r = translate dafny_to_cakemlTheory.cml_get_arr_dim_def;
val r = translate dafny_to_cakemlTheory.cml_get_arr_data_def;

val r = translate astTheory.Apps_def;
val r = translate dafny_to_cakemlTheory.cml_apps_def;
val r = translate dafny_to_cakemlTheory.cml_lets_def;

val r = translate namespaceTheory.mk_id_def;
val r = translate dafny_to_cakemlTheory.cml_fapp_def;

val r = translate dafny_to_cakemlTheory.cml_read_var_def;
val r = translate dafny_to_cakemlTheory.from_un_op_def;
val r = translate dafny_to_cakemlTheory.from_bin_op_def;
val r = translate dafny_to_cakemlTheory.from_lit_def;
val r = translate dafny_to_cakemlTheory.gen_arg_names_def;
val r = translate dafny_to_cakemlTheory.from_exp_def;
val r = translate dafny_to_cakemlTheory.map_from_exp_tup_def;
val r = translate dafny_to_cakemlTheory.from_rhs_exp_def;
val r = translate dafny_to_cakemlTheory.cml_tmp_vname_def;
val r = translate dafny_to_cakemlTheory.assign_single_def;

val r = translate astTheory.Seqs_def;
val r = translate dafny_to_cakemlTheory.par_assign_def;

val r = translate dafny_to_cakemlTheory.to_string_def;
val r = translate dafny_to_cakemlTheory.loop_name_def;
val r = translate dafny_to_cakemlTheory.from_stmt_def;
val r = translate dafny_to_cakemlTheory.set_up_in_refs_def;
val r = translate dafny_to_cakemlTheory.set_up_cml_fun_def;
val r = translate dafny_to_cakemlTheory.from_member_decl_def;

val r = translate locationTheory.unknown_loc_def;
val r = translate dafny_to_cakemlTheory.from_program_def;

val _ = export_theory ();
