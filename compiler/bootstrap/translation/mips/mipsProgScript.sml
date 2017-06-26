open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open compiler64ProgTheory
open mips_targetTheory mipsTheory;
open inliningLib;

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
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
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

val spec_word_bit = word_bit |> ISPEC``foo:word16`` |> SPEC``15n``|> SIMP_RULE std_ss [word_bit_thm] |> CONV_RULE (wordsLib.WORD_CONV)

val defaults =
  [mips_ast_def,mips_encode_def,Encode_def,
   mips_bop_r_def, mips_bop_i_def, mips_memop_def,
   mips_encode_fail_def,
   form1_def,form2_def,form3_def,form4_def,form5_def,form6_def]

val mips_enc_thms =
  mips_enc_def
  |> SIMP_RULE std_ss [FUN_EQ_THM]
  |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss[``:64 asm``])[]
  |> CONJUNCTS
val mips_enc1 = el 1 mips_enc_thms
val mips_enc2 = el 2 mips_enc_thms
val mips_enc3 = el 3 mips_enc_thms
val mips_enc4 = el 4 mips_enc_thms
val mips_enc5 = el 5 mips_enc_thms
val mips_enc6 = el 6 mips_enc_thms

val mips_enc1s =
  mips_enc1
  |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss [``:64 inst``]) defaults
  |> CONJUNCTS

val mips_enc1_1 = el 1 mips_enc1s
val mips_enc1_2 = el 2 mips_enc1s
  |> SIMP_RULE (srw_ss()++LET_ss) ([Ntimes COND_RAND 5,COND_RATOR,spec_word_bit]@defaults)
  |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]
  |> csethm 5

val (binop::shift::rest) = el 3 mips_enc1s |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss [``:64 arith``]) [] |> CONJUNCTS

val (binopreg_aux::binopimm_aux::_) = binop |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss [``:64 reg_imm``]) [FORALL_AND_THM] |> CONJUNCTS |> map (SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss [``:binop``]) [])

val binopreg = binopreg_aux |> CONJUNCTS |> map(fn th => th |> SIMP_RULE (srw_ss()++LET_ss) (defaults) |> wc_simp |> we_simp |> gconv |>SIMP_RULE std_ss [SHIFT_ZERO])

val binopregth = reconstruct_case ``mips_enc (Inst (Arith (Binop b n n0 (Reg n'))))`` (rand o rator o rator o rator o rand o rand o rand) (map (csethm 2) binopreg)

val binopimm = binopimm_aux |> CONJUNCTS |> map(fn th => th
  |> SIMP_RULE (srw_ss()++LET_ss)
               (Q.ISPEC`LIST_BIND`COND_RAND :: COND_RATOR :: word_mul_def :: defaults)
  |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO])

val binopimmth = reconstruct_case ``mips_enc (Inst (Arith (Binop b n n0 (Imm c))))`` (rand o rator o rator o rator o rand o rand o rand) binopimm

val binopth = reconstruct_case ``mips_enc(Inst (Arith (Binop b n n0 r)))`` (rand o rand o rand o rand) [binopregth,binopimmth]

val shiftths =
  shift
  |> SIMP_RULE(srw_ss()++LET_ss++DatatypeSimps.expand_type_quants_ss[``:shift``])
      (Q.ISPEC`(λ(f,n). P f n)` COND_RAND::
       Q.ISPEC`LIST_BIND`COND_RAND ::
       COND_RATOR ::
       mips_sh32_def :: mips_sh_def ::
      defaults)
  |> CONJUNCTS
  |> map (fn th => th |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO])

val shiftth = reconstruct_case ``mips_enc(Inst (Arith (Shift s n n0 n1)))``
  (rand o funpow 3 rator o funpow 3 rand) shiftths

val mips_enc1_3_aux = binopth :: shiftth :: map (fn th => th |> SIMP_RULE (srw_ss()) defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]) rest

val mips_enc1_3 = reconstruct_case ``mips_enc (Inst (Arith a))`` (rand o rand o rand) mips_enc1_3_aux

val mips_enc1_4_aux = el 4 mips_enc1s |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss [``:64 addr``,``:memop``]) defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO] |> CONJUNCTS

val mips_enc1_4 = reconstruct_case ``mips_enc (Inst (Mem m n a))`` (rand o rand o rand) [reconstruct_case ``mips_enc (Inst (Mem m n (Addr n' c)))`` (rand o rator o rator o rand o rand) mips_enc1_4_aux]

val mips_simp1 = reconstruct_case ``mips_enc (Inst i)`` (rand o rand) [mips_enc1_1,mips_enc1_2,mips_enc1_3,mips_enc1_4]

val mips_simp2 = mips_enc2 |> SIMP_RULE (srw_ss() ++ LET_ss) (Once COND_RAND::COND_RATOR::defaults) |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]

val mips_enc3_aux = mips_enc3
  |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss[``:64 reg_imm``])[FORALL_AND_THM]
  |> CONJUNCTS
  |> map (fn th => th
     |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss[``:cmp``])
                  (mips_cmp_def::defaults)
     |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO])

val mips_enc3_1 = el 1 mips_enc3_aux
val mips_enc3_2 = el 2 mips_enc3_aux

val mips_enc3_1_th =
  mips_enc3_1 |> CONJUNCTS
  |> reconstruct_case ``mips_enc (JumpCmp c n (Reg n') c0)``
     (rand o funpow 3 rator o rand)

val mips_enc3_2_th =
  mips_enc3_2 |> CONJUNCTS
  |> reconstruct_case ``mips_enc (JumpCmp c n (Imm c') c0)``
     (rand o funpow 3 rator o rand)

val mips_simp3 =
  reconstruct_case ``mips_enc (JumpCmp c n r c0)`` (rand o rator o rand)
    [mips_enc3_1_th,mips_enc3_2_th]

val mips_simp4 = mips_enc4 |> SIMP_RULE (srw_ss() ++ LET_ss) (Once COND_RAND::COND_RATOR::defaults) |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]

val mips_simp5 = mips_enc5 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]

val mips_simp6 = mips_enc6
  |> SIMP_RULE (srw_ss() ++ LET_ss) (Q.ISPEC`LIST_BIND`COND_RAND :: COND_RATOR :: defaults)
  |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]

val mips_enc_thm = reconstruct_case ``mips_enc i`` rand [mips_simp1,mips_simp2,mips_simp3,mips_simp4,mips_simp5,mips_simp6]

val res = translate mips_enc_thm

val res = translate (mips_config_def |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]|> econv)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
