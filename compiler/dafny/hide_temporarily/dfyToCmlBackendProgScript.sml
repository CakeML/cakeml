(*
 * Program implementing the Dafny to CakeML backend.
 *
 * The program expects a string containing the Dafny program as an S-Expression,
 * and returns a string containing the corresponding CakeML program as an
 * S-Expression.
 *)

open preamble
open endToEndTheory
open ml_translatorLib
open dfyAndCmlTypesProgTheory

val _ = use_long_names:=true;

val _ = new_theory "dfyToCmlBackendProg";

val _ = translation_extends "dfyAndCmlTypesProg";

val _ = translate dafny_utilTheory.bind_def;

(* Copied from to_flatProgScript.sml *)
val _ = translate EL;
val list_el_side = Q.prove(
  `!n xs. list_el_side n xs = (n < LENGTH xs)`,
  Induct THEN Cases_on `xs` THEN ONCE_REWRITE_TAC [fetch "-" "list_el_side_def"]
  THEN FULL_SIMP_TAC (srw_ss()) [])
  |> update_precondition;

val r = translate toCakeMlAstTheory.from_string_def;
val r = translate toCakeMlAstTheory.gen_literal_def;
val r = translate toCakeMlAstTheory.gen_expression_def;
val r = translate toCakeMlAstTheory.gen_statement_def;
val r = translate toCakeMlAstTheory.compile_def;

val r = translate optionTheory.OPTION_BIND_def;

val r = translate toDafnyAstTheory.sxstr_to_str_def;
val r = translate toDafnyAstTheory.sxstr_to_ch_def;
val r = translate toDafnyAstTheory.sxnum_to_num_def;
val r = translate toDafnyAstTheory.sxsym_to_bool_def;
           
(* ^^^ works ^^^ *)

val r = translate toDafnyAstTheory.sxsym_to_opt_def;
val r = translate toDafnyAstTheory.opt_mmap_sexp_list_def;
val r = translate toDafnyAstTheory.opt_mmap_sexp_tuple_def;
val r = translate toDafnyAstTheory.opt_mmap_sexp_tuple_list_def;
val r = translate toDafnyAstTheory.sexp_name_def;
val r = translate toDafnyAstTheory.sexp_ident_def;
val r = translate toDafnyAstTheory.sexp_attribute_def;
val r = translate toDafnyAstTheory.sexp_primitive_def;
val r = translate toDafnyAstTheory.sexp_collKind_def;
val r = translate toDafnyAstTheory.sexp_typeArgBound_def;
val r = translate toDafnyAstTheory.sexp_typeArgDecl_def;
val r = translate toDafnyAstTheory.sexp_newtypeRange_def;
val r = translate toDafnyAstTheory.sexp_unaryOp_def;
val r = translate toDafnyAstTheory.sexp_binOp_def;
val r = translate toDafnyAstTheory.sexp_datatypeType_def;
val r = translate toDafnyAstTheory.sexp_type_def;
val r = translate toDafnyAstTheory.sexp_literal_def;
val r = translate toDafnyAstTheory.sexp_formal_def;
val r = translate toDafnyAstTheory.sexp_callSignature_def;
val r = translate toDafnyAstTheory.sexp_callName_def;
val r = translate toDafnyAstTheory.sexp_statement_def;
val r = translate toDafnyAstTheory.sexp_method_def;
val r = translate toDafnyAstTheory.sexp_field_def;
val r = translate toDafnyAstTheory.sexp_classItem_def;
val r = translate toDafnyAstTheory.sexp_class_def;
val r = translate toDafnyAstTheory.sexp_trait_def;
val r = translate toDafnyAstTheory.sexp_newtype_def;
val r = translate toDafnyAstTheory.sexp_datatypeDtor_def;
val r = translate toDafnyAstTheory.sexp_datatypeCtor_def;
val r = translate toDafnyAstTheory.sexp_datatype_def;
val r = translate toDafnyAstTheory.sexp_module_def;
val r = translate toDafnyAstTheory.sexp_program_def;

val _ = translate dafny_utilTheory.parse_sexp_input_def;

val _ = translate dfy_to_cml_def;

val _ = export_theory ();
