(*
  Translate the compiler explorer parts of the compiler.
*)
Theory explorerProg[no_sig_docs]
Ancestors
  inferProg
Libs
  preamble ml_translatorLib

open preamble
     ml_translatorLib
     inferProgTheory;

val _ = temp_delsimps ["NORMEQ_CONV"]

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

val res = translate jsonLangTheory.encode_str_def;
val res = translate jsonLangTheory.concat_with_def;

val res = translate_no_ind jsonLangTheory.json_to_mlstring_def;

Theorem json_to_mlstring_ind[local]:
  json_to_mlstring_ind
Proof
  rewrite_tac [fetch "-" "json_to_mlstring_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac jsonLangTheory.json_to_mlstring_ind
  \\ metis_tac []
QED

val _ = json_to_mlstring_ind |> update_precondition;

(* displayLang *)

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

Theorem string_imp_thm[local]:
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


val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);
