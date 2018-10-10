open preamble
     ml_translatorLib
     inferProgTheory

val _ = new_theory "explorerProg"

val _ = translation_extends "inferProg";

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

val res = translate presLangTheory.num_to_hex_digit_def;

val num_to_hex_digit_side = prove(
  ``num_to_hex_digit_side n = T``,
  EVAL_TAC \\ fs [])
  |> update_precondition;

val res = translate presLangTheory.num_to_hex_def;

val res = translate
  (presLangTheory.display_word_to_hex_string_def |> INST_TYPE [``:'a``|->``:8``]);
val res = translate
  (presLangTheory.display_word_to_hex_string_def |> INST_TYPE [``:'a``|->``:64``]);

val res = translate displayLangTheory.num_to_json_def;
val res = translate displayLangTheory.trace_to_json_def;
val res = translate displayLangTheory.display_to_json_def;

val res = translate presLangTheory.flat_op_to_display_def;
val res = translate presLangTheory.tap_flat_def;

val res = translate presLangTheory.num_to_varn_def;
val num_to_varn_side = Q.prove(`
  ∀n. num_to_varn_side n ⇔ T`,
  recInduct presLangTheory.num_to_varn_ind \\ rw[] \\
  rw[Once (theorem"num_to_varn_side_def")] \\
  `n MOD 26 < 26` by simp[] \\ decide_tac) |> update_precondition;

val res = translate presLangTheory.tap_flat_def;
val res = translate presLangTheory.tap_pat_def;
val res = translate presLangTheory.tap_clos_def;

(* we can't translate the tap_word bits yet, because that's 32/64 specific.
   that's done in the to_word* scripts. *)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
