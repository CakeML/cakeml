open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open compiler64ProgTheory
open x64_targetTheory x64Theory;

val _ = new_theory "x64Prog"

val _ = translation_extends "compiler64Prog";

val RW = REWRITE_RULE

val _ = add_preferred_thy "-";
val _ = add_preferred_thy "termination";

val NOT_NIL_AND_LEMMA = Q.prove(
  `(b <> [] /\ x) = if b = [] then F else x`,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_thm") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val spec64 = INST_TYPE[alpha|->``:64``]

val conv64_RHS = GEN_ALL o CONV_RULE (RHS_CONV wordsLib.WORD_CONV) o spec64 o SPEC_ALL

val _ = translate (conv64_RHS integer_wordTheory.WORD_LEi)

val _ = register_type``:64 asm_config``

val word_bit_thm = Q.prove(
  `!n w. word_bit n w = ((w && n2w (2 ** n)) <> 0w)`,
  simp [GSYM wordsTheory.word_1_lsl]
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index]
  \\ eq_tac
  \\ rw []
  >- (qexists_tac `n` \\ simp [DECIDE ``0 < a /\ n <= a - 1n ==> n < a``])
  \\ `i = n` by decide_tac
  \\ fs [])

(* word_bit can be inlined into encode (current choice), or translated into a function
val foo = translate ((INST_TYPE[alpha|->``:4``]o SPEC_ALL )th)
*)

(* word_concat *)
val wc_simp = CONV_RULE (wordsLib.WORD_CONV) o SIMP_RULE std_ss [word_concat_def,word_join_def,w2w_w2w,LET_THM]
(* word_extract *)
val we_simp = SIMP_RULE std_ss [word_extract_w2w_mask,w2w_id]

val gconv = CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV)
val econv = CONV_RULE wordsLib.WORD_EVAL_CONV

(* w2w has to be translated for every single use *)
val _ = translate (INST_TYPE[alpha|->``:64``,beta|->``:8``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:4``,beta|->``:8``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:4``,beta|->``:3``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:2``,beta|->``:8``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:3``,beta|->``:4``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:64``,beta|->``:33``] w2w_def)

val _ = translate (e_imm32_def |> we_simp |> econv)

val _ = translate (e_imm8_def |> we_simp |> econv)

val _ = translate (e_ModRM_def |> wc_simp |> we_simp |> SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY,SHIFT_ZERO] |> gconv)

val _ = translate (rex_prefix_def |> wc_simp |> we_simp |> econv)

val _ = translate (e_imm16_def |> we_simp |> econv)
val _ = translate (e_imm64_def |> we_simp |> econv)

val _ = translate (encode_def|>SIMP_RULE std_ss [word_bit_thm] |> wc_simp |> we_simp |> SIMP_RULE std_ss[SHIFT_ZERO] |> gconv)

val _ = translate (x64_ast_def |> we_simp |> gconv)

val total_num2zreg_side = Q.prove(`
  ∀x. total_num2zreg_side x ⇔ T`,
  simp[fetch "-" "total_num2zreg_side_def"]>>
  FULL_SIMP_TAC std_ss [fetch "-" "num2zreg_side_def"]>>
  ntac 2 strip_tac>>
  (* Faster than DECIDE_TAC *)
  Cases_on`x`>>FULL_SIMP_TAC std_ss [ADD1]>>
  ntac 7 (Cases_on`n`>>FULL_SIMP_TAC std_ss [ADD1]>>
  Cases_on`n'`>>FULL_SIMP_TAC std_ss [ADD1])>>
  Cases_on`n`>>fs[])

val x64_ast_side = Q.prove(`
  ∀x. x64_ast_side x ⇔ T`,
  simp[fetch "-" "x64_ast_side_def",total_num2zreg_side]) |> update_precondition

val _ = translate x64_enc_def

val _ = translate (x64_config_def |> gconv)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
