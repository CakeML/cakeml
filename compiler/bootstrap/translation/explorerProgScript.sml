(*
  Translate the compiler explorer parts of the compiler.
*)
open preamble
     ml_translatorLib
     inferProgTheory

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory "explorerProg"

val _ = translation_extends "inferProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "explorerProg");
val _ = ml_translatorLib.use_string_type false;

(* TODO: this is copied in many bootstrap translation files - should be in a lib? *)
fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> CONV_RULE (DEPTH_CONV BETA_CONV)
  in def end

val _ = (find_def_for_const := def_of_const);

val res = translate jsonLangTheory.num_to_hex_digit_def;

val num_to_hex_digit_side = prove(
  ``num_to_hex_digit_side n = T``,
  EVAL_TAC \\ fs [])
  |> update_precondition;

val res = translate jsonLangTheory.encode_str_def;
val res = translate jsonLangTheory.concat_with_def;

val res = translate_no_ind jsonLangTheory.json_to_mlstring_def;

Triviality json_to_mlstring_ind:
  json_to_mlstring_ind
Proof
  rewrite_tac [fetch "-" "json_to_mlstring_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac jsonLangTheory.json_to_mlstring_ind
  \\ metis_tac []
QED

val _ = json_to_mlstring_ind |> update_precondition;

val res = translate presLangTheory.num_to_hex_def;

val res = translate
  (presLangTheory.display_word_to_hex_string_def |> INST_TYPE [``:'a``|->``:8``]);
val res = translate
  (presLangTheory.display_word_to_hex_string_def |> INST_TYPE [``:'a``|->``:64``]);

val res = translate displayLangTheory.trace_to_json_def;
val res = translate displayLangTheory.display_to_json_def;

(* fixme: flat op datatype has been translated with use_string_type, which
   for compatibility here needs that switch on, and looks like it results
   in an unnecessary explode/implode pair *)
val _ = ml_translatorLib.use_string_type true;
val res = translate (presLangTheory.flat_op_to_display_def);
val _ = ml_translatorLib.use_string_type false;

val _ = translate presLangTheory.lang_to_json_def

(* again *)
val _ = ml_translatorLib.use_string_type true;
val r = translate presLangTheory.lit_to_display_def
val _ = ml_translatorLib.use_string_type false;

val r = translate presLangTheory.num_to_varn_def
val num_to_varn_side = Q.prove(`
  ∀n. num_to_varn_side n ⇔ T`,
  recInduct presLangTheory.num_to_varn_ind \\ rw[] \\
  rw[Once (theorem"num_to_varn_side_def")] \\
  `n MOD 26 < 26` by simp[] \\ decide_tac)
  |> update_precondition;

Theorem string_imp_lam:
  string_imp = \s. String (implode s)
Proof
  fs [FUN_EQ_THM,presLangTheory.string_imp_def]
QED

val string_imp = SIMP_RULE bool_ss [string_imp_lam];

val r = translate (presLangTheory.display_num_as_varn_def |> string_imp);
val _ = ml_translatorLib.use_string_type true;
val res = translate (presLangTheory.flat_to_display_def)
val _ = ml_translatorLib.use_string_type false;

val res = translate presLangTheory.tap_flat_def;

val _ = ml_translatorLib.use_string_type true;
val r = translate (presLangTheory.clos_op_to_display_def |> string_imp);
val _ = ml_translatorLib.use_string_type false;

val r = translate (presLangTheory.clos_to_display_def |> string_imp);

val res = translate presLangTheory.tap_clos_def;

val res = translate presLangTheory.tap_data_lang_def;

(* we can't translate the tap_word bits yet, because that's 32/64 specific.
   that's done in the to_word* scripts. *)

(* more parts of the external interface *)
val res = translate presLangTheory.default_tap_config_def;
val res = translate presLangTheory.mk_tap_config_def;
val res = translate presLangTheory.tap_data_mlstrings_def;

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
