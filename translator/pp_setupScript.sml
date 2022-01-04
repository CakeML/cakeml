(*
  Install manually defined components of the pretty-printer.

  Once these components are present, the add-pretty-printer
  pass has the resources it needs to define pretty printers
  for additional types.
*)

open preamble astTheory semanticPrimitivesTheory;
open ml_translatorLib ml_translatorTheory ml_progLib;
open decProgTheory mlprettyprinterTheory;

val _ = new_theory "pp_setup";

val _ = translation_extends "decProg";

val _ = register_type ``: pp_data``;

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  in def end;

val _ = (find_def_for_const := def_of_const);

val res = translate pp_fun_def;
val res = translate pp_exn_def;
val res = translate pp_paren_tuple_def;
val res = translate pp_app_block_def;
val res = translate pp_list_def;
val res = translate pp_string_def;
val res = translate pp_char_def;
val res = translate pp_bool_def;

(* useless pretty-printers for impure types. added here to ensure no type
   errors. should be replaced later in the basis *)
val res = translate pp_ref_def;
val res = translate pp_array_def;
val res = translate pp_word8array_def;
val res = translate pp_vector_def;

(* translate pps for numeric types, which are actually used early. *)
val res = translate mlintTheory.num_to_rev_chars_def;

Triviality tochar_side_dec:
  i < 10 ==> tochar_side i
Proof
  EVAL_TAC \\ simp []
QED

Triviality num_to_rev_chars_side:
  !i j k. num_to_rev_chars_side i j k
Proof
  ho_match_mp_tac mlintTheory.num_to_rev_chars_ind
  \\ rw []
  \\ ONCE_REWRITE_TAC [fetch "-" "num_to_rev_chars_side_def"]
  \\ simp [tochar_side_dec]
QED

val res = update_precondition num_to_rev_chars_side;

val res = translate pp_int_def;
val res = translate pp_word8_def;
val res = translate pp_word64_def;

val _ = export_theory();

