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
val _ = ml_translatorLib.use_sub_check true;

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

(* str_tree and displayLang *)

val r = translate str_treeTheory.v2strs_def;
val r = translate displayLangTheory.display_to_str_tree_def;

(* presLang *)

val res = translate presLangTheory.num_to_hex_def;
val res = translate (presLangTheory.word_to_display_def |> INST_TYPE [``:'a``|->``:8``]);
val res = translate (presLangTheory.word_to_display_def |> INST_TYPE [``:'a``|->``:64``]);

val _ = ml_translatorLib.use_string_type true;
val res = translate presLangTheory.source_to_strs_def;
val _ = ml_translatorLib.use_string_type false;

val _ = ml_translatorLib.use_string_type true;
val res = translate presLangTheory.flat_to_strs_def;
val res = translate presLangTheory.clos_op_to_display_def;
val _ = ml_translatorLib.use_string_type false;

val r = translate presLangTheory.num_to_varn_def
val num_to_varn_side = Q.prove(`
  ∀n. num_to_varn_side n ⇔ T`,
  recInduct presLangTheory.num_to_varn_ind \\ rw[] \\
  rw[Once (theorem"num_to_varn_side_def")] \\
  `n MOD 26 < 26` by simp[] \\ decide_tac)
  |> update_precondition;

val r = presLangTheory.display_num_as_varn_def
          |> REWRITE_RULE [presLangTheory.string_imp_def]
          |> translate;

val r = translate presLangTheory.data_prog_to_display_def;
val r = translate presLangTheory.data_fun_to_display_def;
val r = translate presLangTheory.data_to_strs_def;

val r = translate presLangTheory.bvl_to_display_def;
val r = translate presLangTheory.bvl_fun_to_display_def;
val r = translate presLangTheory.bvl_to_strs_def;

val r = translate presLangTheory.bvi_to_display_def;
val r = translate presLangTheory.bvi_fun_to_display_def;
val r = translate presLangTheory.bvi_to_strs_def;

val r = translate clos_to_bvlTheory.init_code_def;

Triviality bvl_jump_jumplist_side:
  ∀x y. bvl_jump_jumplist_side x y
Proof
  ho_match_mp_tac bvl_jumpTheory.JumpList_ind
  \\ rw [] \\ simp [Once to_bvlProgTheory.bvl_jump_jumplist_side_def]
  \\ Cases_on ‘xs’ \\ fs []
QED

Triviality init_code_side:
  init_code_side x
Proof
  fs [fetch "-" "init_code_side_def",
      to_bvlProgTheory.clos_to_bvl_generate_generic_app_side_def,
      to_bvlProgTheory.bvl_jump_jump_side_def,bvl_jump_jumplist_side]
QED

Triviality string_imp_thm:
  string_imp = λs. String (implode s)
Proof
  fs [FUN_EQ_THM,presLangTheory.string_imp_def]
QED

val _ = ml_translatorLib.use_string_type true;
val r = presLangTheory.clos_to_display_def
          |> REWRITE_RULE [string_imp_thm]
          |> translate

val r = translate presLangTheory.clos_dec_to_display_def;
val r = translate presLangTheory.clos_to_strs_def;

val _ = update_precondition init_code_side;

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
