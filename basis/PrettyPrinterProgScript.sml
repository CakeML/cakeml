(*
  Module providing pretty-printer implementation, and setup
  of the global builtin pretty-printer functions.
*)

Theory PrettyPrinterProg
Ancestors
  mlprettyprinter IntProg[qualified]
Libs
  preamble ml_translatorLib ml_progLib astSyntax
  addPrettyPrintersLib[qualified]

val _ = translation_extends "IntProg"

val previous_prog_pps = get_prog (get_ml_prog_state ())
  |> addPrettyPrintersLib.pps_of_global_tys;

val _ = ml_prog_update (open_module "PrettyPrinter")

val _ = (use_full_type_names := false);
val _ = register_type ``: pp_data``;
val _ = register_type ``: default_type``;

fun tr name def = (
  next_ml_names := [name];
  translate def
)

val _ = ml_prog_update open_local_block;

val res = translate app_intersperse_def;
val res = translate app_list_wrap_def;
val res = translate pp_paren_contents_def;

val _ = translate escape_str_app_list_def;

Theorem escape_str_app_list_side[local]:
  !i s. escape_str_app_list_side i s <=> i <= strlen s
Proof
  recInduct escape_str_app_list_ind
  \\ rw []
  \\ simp [Once (theorem "escape_str_app_list_side_def")]
  \\ Cases_on `str_findi (\c. IS_SOME (char_escape_seq c)) i s`
  \\ fs []
  \\ imp_res_tac mlstringTheory.str_findi_range
  \\ simp []
QED

val res = update_precondition escape_str_app_list_side;

val _ = ml_prog_update open_local_in_block;

val res = tr "toAppList" pp_contents_def;
val res = tr "no_parens" pp_no_parens_def;
val res = tr "token" pp_token_def;
val res = tr "tuple" pp_paren_tuple_def;
val res = tr "spaced_block" pp_spaced_block_def;
val res = tr "app_block" pp_app_block_def;
val res = tr "val_eq" pp_val_eq_def;
val res = tr "val_eq" pp_val_eq_def;
val res = tr "val_hidden_type" pp_val_hidden_type_def;
val res = tr "failure_message" pp_failure_message_def;
val res = tr "unprintable" pp_unprintable_def;

val res = translate pp_list_def;
val res = translate pp_bool_def;

val res = translate pp_char_def;
val res = translate pp_string_def;

val res = translate pp_app_list_def;
val res = translate pp_pp_data_def;

val res = translate pp_default_type_def;

val _ = ml_prog_update close_local_blocks;

val _ = ml_prog_update (close_module NONE);

(* pretty-printers for global (builtin) types, at global scope *)

val res = translate pp_exn_def;
val res = translate pp_unit_def;
val res = translate pp_vector_def;

(* add global names for some printers, esp. those used in pp_pp_data *)
Definition rename_pp_list_def:
  rename_pp_list = pp_list
End
val res = tr "pp_list" rename_pp_list_def;

Definition rename_pp_bool_def:
  rename_pp_bool = pp_bool
End
val res = tr "pp_bool" rename_pp_bool_def;

Definition rename_pp_char_def:
  rename_pp_char = pp_char
End
val res = tr "pp_char" rename_pp_char_def;

Definition rename_pp_string_def:
  rename_pp_string = pp_string
End
val res = tr "pp_string" rename_pp_string_def;

Definition rename_pp_app_list_def:
  rename_pp_app_list = pp_app_list
End
val res = tr "pp_app_list" rename_pp_app_list_def;

(* useless pretty-printers for impure types.
   should be replaced later in the basis *)
val res = translate pp_ref_def;
val res = translate pp_array_def;
val res = translate pp_word8array_def;

(* candle needs constants in the basis to be defined as literals, no funcalls *)
val res = translate (REWRITE_RULE [pp_token_def] pp_fun_def);

(* pretty printers for numeric types *)
val res = translate pp_int_def;
val res = translate pp_word8_def;
val res = translate pp_word64_def;

(* setup pretty-printers for previously existing global types *)
val _ = ml_prog_update (addPrettyPrintersLib.add_pps previous_prog_pps)
