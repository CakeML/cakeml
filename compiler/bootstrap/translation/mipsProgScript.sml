open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open compiler64ProgTheory
open mips_targetTheory mipsTheory;

val _ = new_theory "mipsProg"

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
val _ = translate (conv64_RHS integer_wordTheory.WORD_LTi)

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

(* word_concat *)
val wc_simp = CONV_RULE (wordsLib.WORD_CONV) o SIMP_RULE std_ss [word_concat_def,word_join_def,w2w_w2w,LET_THM]
(* word_extract *)
val we_simp = SIMP_RULE std_ss [word_extract_w2w_mask,w2w_id]
val wcomp_simp = SIMP_RULE std_ss [word_2comp_def]
val gconv = CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV)
val econv = CONV_RULE wordsLib.WORD_EVAL_CONV

(* w2w has to be translated for every single use *)
val _ = translate (INST_TYPE[alpha|->``:5``,beta|->``:32``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:16``,beta|->``:32``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:3``,beta|->``:32``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:26``,beta|->``:32``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:6``,beta|->``:32``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:32``,beta|->``:8``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:32``,beta|->``:64``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:64``,beta|->``:16``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:64``,beta|->``:32``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:32``,beta|->``:16``] w2w_def)

(* This inlines and simplifies all the form*s, might be a bad idea... *)
val _ = translate (Encode_def |> SIMP_RULE std_ss [form1_def,form2_def,form3_def,form4_def,form5_def,form6_def] |> CONV_RULE (wordsLib.WORD_CONV) |> we_simp |> SIMP_RULE std_ss[SHIFT_ZERO] |> gconv)

val _ = translate (mips_encode_def |> we_simp |> econv)

val spec_word_bit = word_bit |> ISPEC``foo:word16`` |> SPEC``15n``|> SIMP_RULE std_ss [word_bit_thm] |> CONV_RULE (wordsLib.WORD_CONV)

val _ = translate (mips_ast_def |> CONV_RULE (wordsLib.WORD_CONV) |> we_simp |> SIMP_RULE std_ss[SHIFT_ZERO] |> SIMP_RULE std_ss[spec_word_bit,word_mul_def]|> econv)

val mips_ast_side = Q.prove(`
  ∀x. mips_ast_side x ⇔ T`,
  simp[fetch "-" "mips_ast_side_def"]>>rw[]>>
  EVAL_TAC) |> update_precondition

val _ = translate (mips_enc_def |> SIMP_RULE std_ss [o_DEF,FUN_EQ_THM])

val _ = translate (mips_config_def |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]|> econv)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
