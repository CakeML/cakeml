open preamble
     ml_translatorLib
     to_dataProgTheory

val _ = new_theory "explorerProg"

val _ = translation_extends "to_dataProg";

val mem_to_string_lemma = prove(
  ``mem_to_string x =
    Append (Append (Append (List "\"") (List (FST x))) (List "\":"))
       (json_to_string (SND x))``,
  Cases_on `x` \\ simp [Once jsonLangTheory.json_to_string_def] \\ fs []);

val res = translate
  (jsonLangTheory.json_to_string_def
   |> CONJUNCT1 |> SPEC_ALL
   |> (fn th => LIST_CONJ [th,mem_to_string_lemma]));

val res = translate presLangTheory.num_to_hex_digit_def;

val num_to_hex_digit_side = prove(
  ``preslang_num_to_hex_digit_side n = T``,
  EVAL_TAC \\ fs [])
  |> update_precondition;

val res = translate presLangTheory.num_to_hex_def;

val res = translate
  (presLangTheory.word_to_hex_string_def |> INST_TYPE [``:'a``|->``:8``]);
val res = translate
  (presLangTheory.word_to_hex_string_def |> INST_TYPE [``:'a``|->``:64``]);

val res = translate displayLangTheory.num_to_json_def;
val res = translate displayLangTheory.trace_to_json_def;
val res = translate displayLangTheory.display_to_json_def;

val res1 = translate presLangTheory.mod_to_json_def;
val res2 = translate presLangTheory.con_to_json_def;
val res3 = translate presLangTheory.dec_to_json_def;
val res4 = translate presLangTheory.exh_to_json_def;
val res5 = translate presLangTheory.pat_to_json_def;
val res6 = translate presLangTheory.clos_to_json_def;
val res7 = translate presLangTheory.clos_to_json_table_def;

val () = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
