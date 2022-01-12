(*
  Module providing pretty-printer implementation, and setup
  of the global builtin pretty-printer functions.
*)
open
  preamble
  ml_translatorLib
  ml_progLib
  mlprettyprinterTheory
  astSyntax
local open IntProgTheory in end

val _ = (
  new_theory "PrettyPrinterProg";
  translation_extends "IntProg"
)

val existing_types = get_prog (get_ml_prog_state ()) |> find_terms is_Dtype;

val _ = ml_prog_update (open_module "PrettyPrinter")
val _ = register_type ``: pp_data``;

fun tr name def = (
  next_ml_names := [name];
  translate def
)

val _ = ml_prog_update open_local_block;

val res = translate app_intersperse_def;
val res = translate app_list_wrap_def;
val res = translate ppd_paren_contents_def;

val _ = ml_prog_update open_local_in_block;

val res = tr "toAppList" ppd_contents_def;
val res = tr "token" ppd_token_def;
val res = tr "paren_tuple" pp_paren_tuple_def;
val res = tr "app_block" pp_app_block_def;
val res = translate pp_list_def;
val res = translate pp_bool_def;
val res = translate pp_string_def;

val res = translate pp_app_list_def;
val res = translate pp_pp_data_def;

val _ = ml_prog_update close_local_blocks;

val _ = ml_prog_update (close_module NONE);

(* pretty-printers for global (builtin) types, at global scope *)

val res = translate pp_exn_def;
val res = translate pp_char_def;
val res = translate pp_vector_def;

(* add global names for the printers needed to define pp_pp_data *)
Definition rename_pp_list_def:
  rename_pp_list = pp_list
End
val res = tr "pp_list" rename_pp_list_def;

Definition rename_pp_bool_def:
  rename_pp_bool = pp_bool
End
val res = tr "pp_bool" rename_pp_bool_def;

Definition rename_pp_string_def:
  rename_pp_string = pp_string
End
val res = tr "pp_string" rename_pp_string_def;

(* useless pretty-printers for impure types.
   should be replaced later in the basis *)
val res = translate pp_ref_def;
val res = translate pp_array_def;
val res = translate pp_word8array_def;
val res = translate pp_fun_def;

(* pretty printers for numeric types *)
val res = translate pp_int_def;
val res = translate pp_word8_def;
val res = translate pp_word64_def;

(* install pretty-printers for previously existing types *)
(* (e.g. from decProg and other early translator setup) *)

val pps_for_dec_tm = pps_for_dec_def |> BODY_CONJUNCTS |> hd
    |> concl |> lhs |> strip_comb |> fst
fun dec_pps tm = mk_comb (pps_for_dec_tm, tm)
val decss = listSyntax.mk_list (map dec_pps existing_types, decs_ty)
val pps_eval = ``FLAT ^decss`` |> EVAL
val pps_fin = rhs (concl pps_eval) |> listSyntax.dest_list |> fst

fun add_pps pps prog_st = foldl (fn (pp, prog_st) => add_dec pp I prog_st) prog_st pps

val _ = ml_prog_update (add_pps pps_fin)

val _ = export_theory ()
