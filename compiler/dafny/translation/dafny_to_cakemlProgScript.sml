(*
 * Translates definitions to convert Dafny's AST into CakeML's AST.
 *)

open preamble ml_translatorLib
open sexp_to_dafnyProgTheory

val _ = new_theory "dafny_to_cakemlProg";

val _ = translation_extends "sexp_to_dafnyProg";

val r = translate locationTheory.unknown_loc_def;
val r = translate DROP; (* for strip_prefix_def *)

val r = translate dafny_to_cakemlTheory.int_to_string_def;
val r = translate dafny_to_cakemlTheory.num_to_string_def;
val r = translate dafny_to_cakemlTheory.string_to_int_def;
val r = translate dafny_to_cakemlTheory.string_to_num_def;
val r = translate dafny_to_cakemlTheory.strip_prefix_def;
val r = translate dafny_to_cakemlTheory.is_Eq_def;
val r = translate dafny_to_cakemlTheory.is_Seq_def;
val r = translate dafny_to_cakemlTheory.is_moditem_module_def;
val r = translate dafny_to_cakemlTheory.is_moditem_class_def;
val r = translate dafny_to_cakemlTheory.is_moditem_trait_def;
val r = translate dafny_to_cakemlTheory.is_moditem_newtype_def;
val r = translate dafny_to_cakemlTheory.is_moditem_synonymtype_def;
val r = translate dafny_to_cakemlTheory.is_moditem_datatype_def;
val r = translate dafny_to_cakemlTheory.dest_Array_def;
val r = translate dafny_to_cakemlTheory.dest_Arrow_def;
val r = translate dafny_to_cakemlTheory.dest_singleton_list_def;
val r = translate dafny_to_cakemlTheory.dest_Seq_def;
val r = translate dafny_to_cakemlTheory.dest_Module_def;
val r = translate dafny_to_cakemlTheory.dest_Name_def;
val r = translate dafny_to_cakemlTheory.dest_SOME_def;
val r = translate dafny_to_cakemlTheory.cml_ref_ass_def;
val r = translate dafny_to_cakemlTheory.cml_ref_def;
val r = translate dafny_to_cakemlTheory.cml_list_def;
val r = translate dafny_to_cakemlTheory.string_to_cml_char_list_def;
val r = translate dafny_to_cakemlTheory.cml_fapp_aux_def;
val r = translate dafny_to_cakemlTheory.cml_fapp_def;
val r = translate dafny_to_cakemlTheory.cml_id_def;
val r = translate dafny_to_cakemlTheory.cml_tuple_def;
val r = translate dafny_to_cakemlTheory.cml_tuple_select_def;
val r = translate dafny_to_cakemlTheory.zip_with_def;
val r = translate dafny_to_cakemlTheory.return_ref_name_def;
val r = translate dafny_to_cakemlTheory.varN_from_formal_def;
val r = translate dafny_to_cakemlTheory.internal_varN_from_formal_def;
val r = translate dafny_to_cakemlTheory.internal_varN_from_varName_def;
val r = translate dafny_to_cakemlTheory.cml_option_def;
val r = translate dafny_to_cakemlTheory.normalize_type_def;
val r = translate dafny_to_cakemlTheory.compose_all_def;
val r = translate dafny_to_cakemlTheory.cml_tuple_to_string_list_def;
val r = translate dafny_to_cakemlTheory.raise_return_def;
val r = translate dafny_to_cakemlTheory.raise_break_def;
val r = translate dafny_to_cakemlTheory.add_break_handle_def;
val r = translate dafny_to_cakemlTheory.raise_labeled_break_def;
val r = translate dafny_to_cakemlTheory.add_labeled_break_handle_def;
val r = translate dafny_to_cakemlTheory.cml_while_name_def;
val r = translate dafny_to_cakemlTheory.cml_get_arr_def;
val r = translate dafny_to_cakemlTheory.first_param_def;
val r = translate dafny_to_cakemlTheory.fun_from_params_def;
val r = translate dafny_to_cakemlTheory.fun_from_outs_def;
val r = translate dafny_to_cakemlTheory.ref_from_params_def;
val r = translate dafny_to_cakemlTheory.gen_preamble_aux_def;
val r = translate dafny_to_cakemlTheory.gen_preamble_def;
val r = translate dafny_to_cakemlTheory.gen_epilogue_aux_def;
val r = translate dafny_to_cakemlTheory.gen_epilogue_def;
val r = translate dafny_to_cakemlTheory.to_string_fun_def;
val r = translate dafny_to_cakemlTheory.dest_resolvedType_def;
val r = translate dafny_to_cakemlTheory.arb_value_def;
val r = translate dafny_to_cakemlTheory.add_return_ref_def;
val r = translate dafny_to_cakemlTheory.from_varName_def;
val r = translate dafny_to_cakemlTheory.from_name_def;
val r = translate dafny_to_cakemlTheory.from_ident_def;
val r = translate dafny_to_cakemlTheory.from_literal_def;
val r = translate dafny_to_cakemlTheory.type_from_formals_def;
val r = translate dafny_to_cakemlTheory.call_type_env_from_class_body_def;
val r = translate dafny_to_cakemlTheory.tuple_len_def;
val r = translate dafny_to_cakemlTheory.path_from_companion_def;
val r = translate dafny_to_cakemlTheory.gen_call_name_def;
val r = translate dafny_to_cakemlTheory.handle_return_def;
val r = translate_no_ind dafny_to_cakemlTheory.from_expression_def; (* TODO *)
val r = translate dafny_to_cakemlTheory.from_classItem_def;
val r = translate dafny_to_cakemlTheory.from_classlist_def;
val r = translate dafny_to_cakemlTheory.from_module_def;
val r = translate dafny_to_cakemlTheory.map_from_module_def;
val r = translate dafny_to_cakemlTheory.find_main_def;
val r = translate dafny_to_cakemlTheory.compile_def;
val r = translate dafny_to_cakemlTheory.unpack_def;

val _ = export_theory ();
