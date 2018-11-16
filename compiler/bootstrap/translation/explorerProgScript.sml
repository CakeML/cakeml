open preamble
     ml_translatorLib
     inferProgTheory

val _ = new_theory "explorerProg"

val _ = translation_extends "inferProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "explorerProg");

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

val res = translate jsonLangTheory.escape_def;
val res = translate jsonLangTheory.concat_with_def;

val mem_to_string_lemma = prove(
  ``mem_to_string x =
    Append (Append (Append (List "\"") (List (FST x))) (List "\":"))
       (json_to_string (SND x))``,
  Cases_on `x` \\ simp [Once jsonLangTheory.json_to_string_def] \\ fs []);

val res = translate_no_ind
  (jsonLangTheory.json_to_string_def
   |> CONJUNCT1 |> SPEC_ALL
   |> (fn th => LIST_CONJ [th,mem_to_string_lemma]));

val ind_lemma = Q.prove(
  `^(first is_forall (hyp res))`,
  rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ fs [])
  |> update_precondition;

(*

val res = translate presLangTheory.num_to_hex_digit_def;

val num_to_hex_digit_side = prove(
  ``num_to_hex_digit_side n = T``,
  EVAL_TAC \\ fs [])
  |> update_precondition;

val res = translate presLangTheory.num_to_hex_def;

val res = translate
  (presLangTheory.word_to_hex_string_def |> INST_TYPE [``:'a``|->``:8``]);
val res = translate
  (presLangTheory.word_to_hex_string_def |> INST_TYPE [``:'a``|->``:64``]);

*)

val res = translate displayLangTheory.num_to_json_def;
val res = translate displayLangTheory.trace_to_json_def;
val res = translate displayLangTheory.display_to_json_def;

(*

val res = translate presLangTheory.op_to_display_def;

val op_to_display_side = Q.prove(
  `∀x. op_to_display_side x = T`,
  recInduct presLangTheory.op_to_display_ind \\ rw[] \\
  rw[Once (theorem"op_to_display_side_def")] \\
  EVAL_TAC) |> update_precondition;

val res = translate presLangTheory.pres_to_display_def;
val res = translate presLangTheory.lang_to_json_def;

val res1 = translate presLangTheory.mod_to_json_def;
val res2 = translate presLangTheory.con_to_json_def;
val res3 = translate presLangTheory.dec_to_json_def;
val res4 = translate presLangTheory.exh_to_json_def;

val res = translate presLangTheory.num_to_varn_def;
val num_to_varn_side = Q.prove(`
  ∀n. num_to_varn_side n ⇔ T`,
  recInduct presLangTheory.num_to_varn_ind \\ rw[] \\
  rw[Once (theorem"num_to_varn_side_def")] \\
  `n MOD 26 < 26` by simp[] \\ decide_tac) |> update_precondition;

val res5 = translate presLangTheory.pat_to_json_def;
val res6 = translate presLangTheory.clos_to_json_def;
val res7 = translate presLangTheory.clos_to_json_table_def;

*)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
