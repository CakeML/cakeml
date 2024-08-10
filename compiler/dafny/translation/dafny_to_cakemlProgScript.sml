(*
 * Translates definitions to convert Dafny's AST into CakeML's AST.
 *)

open preamble ml_translatorLib
open sexp_to_dafnyProgTheory

val _ = new_theory "dafny_to_cakemlProg";

val _ = translation_extends "sexp_to_dafnyProg";

val r = translate locationTheory.unknown_loc_def;

val r = translate dafny_to_cakemlTheory.cml_list_def;
val r = translate dafny_to_cakemlTheory.string_to_cml_char_list_def;
val r = translate dafny_to_cakemlTheory.cml_fapp_aux_def;
val r = translate dafny_to_cakemlTheory.cml_fapp_def;
val r = translate dafny_to_cakemlTheory.raise_return_def;
val r = translate dafny_to_cakemlTheory.raise_break_def;
val r = translate dafny_to_cakemlTheory.add_break_handle_def;
val r = translate dafny_to_cakemlTheory.raise_labeled_break_def;
val r = translate dafny_to_cakemlTheory.add_labeled_break_handle_def;
val r = translate dafny_to_cakemlTheory.cml_while_name_def;
val r = translate dafny_to_cakemlTheory.is_DeclareVar_def;
val r = translate dafny_to_cakemlTheory.is_Eq_def;
val r = translate dafny_to_cakemlTheory.is_Seq_def;
val r = translate dafny_to_cakemlTheory.dest_Seq_def;
val r = translate dafny_to_cakemlTheory.dest_Name_def;
val r = translate dafny_to_cakemlTheory.dest_Ident_def;
val r = translate dafny_to_cakemlTheory.dest_DeclareVar_def;
val r = translate dafny_to_cakemlTheory.dest_SOME_def;
val r = translate dafny_to_cakemlTheory.dest_Method_def;
val r = translate dafny_to_cakemlTheory.call_type_name_def;
val r = translate dafny_to_cakemlTheory.from_string_def;
val r = translate dafny_to_cakemlTheory.cml_ref_ass_def;
val r = translate dafny_to_cakemlTheory.cml_ref_def;
val r = translate dafny_to_cakemlTheory.varN_from_formal_def;
val r = translate dafny_to_cakemlTheory.internal_varN_from_formal_def;
val r = translate dafny_to_cakemlTheory.internal_varN_from_ident_def;
val r = translate dafny_to_cakemlTheory.replace_string_type_def;
val r = translate dafny_to_cakemlTheory.arb_value_def;
val r = translate dafny_to_cakemlTheory.from_name_def;
val r = translate dafny_to_cakemlTheory.from_ident_def;
val r = translate dafny_to_cakemlTheory.method_is_function_def;
val r = translate dafny_to_cakemlTheory.method_is_method_def;
val r = translate dafny_to_cakemlTheory.unescape_string_def;
val r = translate dafny_to_cakemlTheory.from_literal_def;
val r = translate dafny_to_cakemlTheory.call_type_env_def;
val r = translate dafny_to_cakemlTheory.dafny_type_of_def;
val r = translate dafny_to_cakemlTheory.from_assignLhs_def;
val r = translate dafny_to_cakemlTheory.from_callName_def;
val r = translate dafny_to_cakemlTheory.from_expression_def;
val r = translate dafny_to_cakemlTheory.to_string_fun_def;
val r = translate dafny_to_cakemlTheory.is_indep_stmt_def;
val r = translate dafny_to_cakemlTheory.from_stmts_def;
val r = translate dafny_to_cakemlTheory.param_type_env_def;
val r = translate dafny_to_cakemlTheory.env_and_epilogue_from_outs_def;
val r = translate dafny_to_cakemlTheory.fun_from_outs_def;
val r = translate dafny_to_cakemlTheory.fun_from_params_def;
val r = translate dafny_to_cakemlTheory.ref_from_params_def;
val r = translate dafny_to_cakemlTheory.gen_param_preamble_epilogue_def;
val r = translate dafny_to_cakemlTheory.gen_param_preamble_def;
val r = translate dafny_to_cakemlTheory.process_function_body_def;
val r = translate dafny_to_cakemlTheory.process_method_body_def;
val r = translate dafny_to_cakemlTheory.from_classItem_def;
val r = translate dafny_to_cakemlTheory.is_moditem_module_def;
val r = translate dafny_to_cakemlTheory.is_moditem_class_def;
val r = translate dafny_to_cakemlTheory.is_moditem_trait_def;
val r = translate dafny_to_cakemlTheory.is_moditem_newtype_def;
val r = translate dafny_to_cakemlTheory.is_moditem_datatype_def;
val r = translate dafny_to_cakemlTheory.body_from_classlist_def;
val r = translate dafny_to_cakemlTheory.compile_def;
val r = translate dafny_to_cakemlTheory.unpack_def;

val _ = export_theory ();
