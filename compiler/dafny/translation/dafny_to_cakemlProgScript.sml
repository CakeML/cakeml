(*
 * Translates definitions to convert Dafny's AST into CakeML's AST.
 *)

open preamble ml_translatorLib
open sexp_to_dafnyProgTheory

val _ = new_theory "dafny_to_cakemlProg";

val _ = translation_extends "sexp_to_dafnyProg";

val r = translate locationTheory.unknown_loc_def;

val r = translate dafny_to_cakemlTheory.from_string_def;
val r = translate dafny_to_cakemlTheory.dest_Name_def;
val r = translate dafny_to_cakemlTheory.from_literal_def;
val r = translate dafny_to_cakemlTheory.dafny_type_of_def;
val r = translate dafny_to_cakemlTheory.from_expression_def;
val r = translate dafny_to_cakemlTheory.arb_value_def;
val r = translate dafny_to_cakemlTheory.from_InitVal_def;
val r = translate dafny_to_cakemlTheory.is_indep_stmt_def;
val r = translate dafny_to_cakemlTheory.from_name_def;
val r = translate dafny_to_cakemlTheory.from_ident_def;
val r = translate dafny_to_cakemlTheory.from_callName_def;
val r = translate dafny_to_cakemlTheory.from_assignLhs_def;
val r = translate dafny_to_cakemlTheory.cml_fapp_aux_def;
val r = translate dafny_to_cakemlTheory.cml_fapp_def;
val r = translate dafny_to_cakemlTheory.from_indep_stmt_def;
val r = translate dafny_to_cakemlTheory.is_DeclareVar_def;
val r = translate dafny_to_cakemlTheory.dest_DeclareVar_def;
val r = translate dafny_to_cakemlTheory.dest_SOME_def;
val r = translate dafny_to_cakemlTheory.from_stmts_def;
val r = translate dafny_to_cakemlTheory.varN_from_formal_def;
val r = translate dafny_to_cakemlTheory.internal_varN_from_formal_def;
val r = translate dafny_to_cakemlTheory.param_defs_from_formals_def;
val r = translate dafny_to_cakemlTheory.declare_init_param_refs_def;
val r = translate dafny_to_cakemlTheory.method_preamble_from_formal_def;
val r = translate dafny_to_cakemlTheory.initial_type_env_def;
val r = translate dafny_to_cakemlTheory.from_method_def;
val r = translate dafny_to_cakemlTheory.from_classItem_def;
val r = translate dafny_to_cakemlTheory.compile_def;
val r = translate dafny_to_cakemlTheory.unpack_def;

val _ = export_theory ();
