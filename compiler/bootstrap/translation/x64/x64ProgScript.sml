open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open compiler64ProgTheory
open x64_targetTheory x64Theory;
open inliningLib;

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
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val spec64 = INST_TYPE[alpha|->``:64``]

val conv64_RHS = GEN_ALL o CONV_RULE (RHS_CONV wordsLib.WORD_CONV) o spec64 o SPEC_ALL

val _ = translate (conv64_RHS integer_wordTheory.WORD_LEi)

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

val zreg2num_totalnum2zerg = Q.prove(`
  Zreg2num (total_num2Zreg n) = if n < 16 then n else 0`,
  EVAL_TAC>>IF_CASES_TAC>>fs[Zreg2num_num2Zreg]);

val Zbinop_name2num_x64_sh = Q.prove(`
  ∀s.Zbinop_name2num (x64_sh s) =
  case s of
    Lsl => 12
  | Lsr => 13
  | Asr => 15
  | Ror => 9`,  Cases>>EVAL_TAC);

val x64_sh_notZtest = Q.prove(`
  ∀s.(x64_sh s) ≠ Ztest `,Cases>>EVAL_TAC);

val exh_if_collapse = Q.prove(`
  ((if P then Ztest else Zcmp) = Ztest) ⇔ P `,rw[]);

val is_rax_zr_thm = Q.prove(`
  is_rax (Zr (total_num2Zreg n)) ⇔
  n = 0 ∨ n ≥ 16`,
  rw[is_rax_def]>>
  EVAL_TAC>>rw[]>>
  rpt(Cases_on`n`>>EVAL_TAC>>fs[]>>
  Cases_on`n'`>>EVAL_TAC>>fs[]))

(* commute list case, option case and if *)
val case_ifs = Q.prove(`
  ((case
    if P then
      l1
    else l2
  of
    [] => A
  | ls => B ls) = if P then case l1 of [] => A | ls => B ls else case l2 of [] => A | ls => B ls)`,rw[])

val case_ifs2 = Q.prove(`
  ((case
    if P then
      SOME (a,b,c)
    else NONE
  of
    NONE => A
  | SOME (a,b,c) => B a b c) = if P then B a b c else A)
  `,
  rw[])

val if_neq = Q.prove(`
  (if P then [x] else []) ≠ [] ⇔ P`,
  rw[])

val fconv = SIMP_RULE (srw_ss()) [SHIFT_ZERO,case_ifs,case_ifs2,if_neq]

val defaults = [x64_ast_def,x64_encode_def,encode_def,e_rm_reg_def,e_gen_rm_reg_def,e_ModRM_def,e_opsize_def,e_imm32_def,rex_prefix_def,x64_dec_fail_def,e_opc_def,e_rax_imm_def,e_rm_imm_def,asmSemTheory.is_test_def,x64_cmp_def,e_opsize_imm_def,e_imm8_def,e_rm_imm8_def,not_byte_def,e_imm16_def,e_imm64_def,Zsize_width_def,x64_bop_def,zreg2num_totalnum2zerg,e_imm_8_32_def,Zbinop_name2num_x64_sh,x64_sh_notZtest,exh_if_collapse,is_rax_zr_thm]

val x64_enc_thms =
  x64_enc_def
  |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss[``:64 asm``])[]
  |> CONJUNCTS
val x64_enc1 = el 1 x64_enc_thms
val x64_enc2 = el 2 x64_enc_thms
val x64_enc3 = el 3 x64_enc_thms
val x64_enc4 = el 4 x64_enc_thms
val x64_enc5 = el 5 x64_enc_thms
val x64_enc6 = el 6 x64_enc_thms

val x64_enc1s = x64_enc1 |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss [``:64 inst``]) defaults |> CONJUNCTS

val x64_enc1_1 = el 1 x64_enc1s

val simp_rw = Q.prove(`
  (if ((1w:word4 && n2w (if n < 16 then n else 0) ⋙ 3) = 1w) then 1w else 0w:word4) =
  (1w && n2w (if n < 16 then n else 0) ⋙ 3)`,
  rw[]>>fs[]>>
  blastLib.FULL_BBLAST_TAC);

val x64_enc1_2 = el 2 x64_enc1s |> wc_simp |> we_simp |> gconv |> bconv |>
 SIMP_RULE std_ss [SHIFT_ZERO,Q.ISPEC`Zsize_CASE` COND_RAND,COND_RATOR,Zsize_case_def] |> fconv |> SIMP_RULE std_ss[Once COND_RAND,simp_rw] |> csethm 2

val (binop::shift::rest) = el 3 x64_enc1s |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss [``:64 arith``]) [] |> CONJUNCTS

val (binopreg_aux::binopimm_aux::_) = binop |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss [``:64 reg_imm``]) [FORALL_AND_THM] |> CONJUNCTS |> map (SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss [``:binop``]) [])

(* TODO: simplify further? *)
val binopreg = binopreg_aux |> CONJUNCTS |> map(fn th => th |> SIMP_RULE (srw_ss()++LET_ss) ((Q.ISPEC `x64_encode` COND_RAND) ::defaults) |> wc_simp |> we_simp |> gconv |> bconv |> fconv)

val binopregth = reconstruct_case ``x64_enc (Inst (Arith (Binop b n n0 (Reg n'))))`` (rand o rator o rator o rator o rand o rand o rand) (map (csethm 2) binopreg)

val binopimm = binopimm_aux |> CONJUNCTS |> map(fn th => th |> SIMP_RULE (srw_ss()++LET_ss) ((Q.ISPEC `x64_encode` COND_RAND) ::defaults) |> wc_simp |> we_simp |> gconv |> bconv |> fconv)

val binopimmth = reconstruct_case ``x64_enc (Inst (Arith (Binop b n n0 (Imm c))))`` (rand o rator o rator o rator o rand o rand o rand) (map (csethm 3) binopimm)

val binopth = reconstruct_case ``x64_enc(Inst (Arith (Binop b n n0 r)))`` (rand o rand o rand o rand) [binopregth,binopimmth]

val shiftths =
  shift
  |> SIMP_RULE(srw_ss()++LET_ss++DatatypeSimps.expand_type_quants_ss[``:shift``])
      (x64_sh_def ::
      defaults)
  |> CONJUNCTS
  |> map (fn th => th |> wc_simp |> we_simp |> gconv
  |> bconv |> fconv |> csethm 3)

val shiftth = reconstruct_case ``x64_enc(Inst (Arith (Shift s n n0 n1)))``
  (rand o funpow 3 rator o funpow 3 rand) shiftths

val x64_enc1_3_aux = binopth :: shiftth:: map (fn th => th |> SIMP_RULE (srw_ss()) defaults |> wc_simp |> we_simp |> gconv |> bconv |> fconv |> csethm 3) rest

val x64_enc1_3 = reconstruct_case ``x64_enc (Inst (Arith a))`` (rand o rand o rand) x64_enc1_3_aux

val x64_enc1_4_aux = el 4 x64_enc1s |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss [``:64 addr``,``:memop``]) defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO] |> CONJUNCTS

(*TODO: can commute the NONE and if *)
val x64_enc1_4 = reconstruct_case ``x64_enc (Inst (Mem m n a))`` (rand o rand o rand) [reconstruct_case ``x64_enc (Inst (Mem m n (Addr n' c)))`` (rand o rator o rator o rand o rand) (map (csethm 2 o fconv o bconv) x64_enc1_4_aux)]

val x64_enc1_5 = el 5 x64_enc1s;

val x64_simp1 = reconstruct_case ``x64_enc (Inst i)`` (rand o rand) [x64_enc1_1,x64_enc1_2,x64_enc1_3,x64_enc1_4,x64_enc1_5]
 |> SIMP_RULE std_ss [Q.ISPEC `Zbinop_name2num` COND_RAND,Zbinop_name2num_thm]

val x64_simp2 = x64_enc2 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults |> wc_simp |> we_simp |> gconv |> bconv |> fconv

val x64_enc3_aux = x64_enc3
  |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss[``:64 reg_imm``])[FORALL_AND_THM]
  |> CONJUNCTS
  |> map (fn th => th
     |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss[``:cmp``])
                  (Q.ISPEC `LIST_BIND` COND_RAND:: COND_RATOR::word_bit_thm::defaults)
     |> wc_simp |> we_simp |> gconv)

val x64_enc3_1 = el 1 x64_enc3_aux
val x64_enc3_2 = el 2 x64_enc3_aux |> SIMP_RULE (srw_ss()) [word_mul_def, Q.ISPEC `w2n` COND_RAND] |> gconv

val x64_enc3_1_th =
  x64_enc3_1 |> CONJUNCTS |> map (fconv o bconv)
  |> reconstruct_case ``x64_enc (JumpCmp c n (Reg n') c0)``
     (rand o funpow 3 rator o rand)

(*bconv takes too long on this one*)
fun avoidp t =
if wordsSyntax.is_word_le t then
  let val (l,r) = wordsSyntax.dest_word_compare t in
    l = ``0xFFFFFFFF80000000w:word64``
  end
else if is_conj t then
  let val(l,r) = dest_conj t in
    avoidp l andalso avoidp r
  end
else
  false

val case_append = Q.prove(`
  (case A ++ [B;C] ++ D of [] => E | ls => ls) = A++[B;C]++D`,
  EVERY_CASE_TAC>>fs[]);

val x64_enc3_2_th =
  x64_enc3_2 |> CONJUNCTS
  |> map (csethm 2 o SIMP_RULE (srw_ss()) [case_append] o fconv o bconv_gen false avoidp)
  |> reconstruct_case ``x64_enc (JumpCmp c n (Imm c') c0)``
     (rand o funpow 3 rator o rand)

val x64_simp3 =
  reconstruct_case ``x64_enc (JumpCmp c n r c0)`` (rand o rator o rand)
    [x64_enc3_1_th,x64_enc3_2_th]

val x64_simp4 = x64_enc4 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]

val case_append2 = Q.prove(`
  (case A ++ [B;C] of [] => E | ls => ls) = A++[B;C]`,
  EVERY_CASE_TAC>>fs[]);

val x64_simp5 = x64_enc5 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO] |> bconv |> fconv |> SIMP_RULE (srw_ss())[case_append2]

val x64_simp6 = x64_enc6 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO] |>bconv |> csethm 2

val x64_enc_thm = reconstruct_case ``x64_enc i`` rand [x64_simp1,x64_simp2,x64_simp3,x64_simp4,x64_simp5,x64_simp6]

(* the manual translation of w2w should no longer be necessary
val w2ws = mk_set(map type_of ((find_terms (fn t => same_const ``w2w`` t)) (concl x64_enc_thm)))

val res = map (fn ty => let val (l,r) = dom_rng ty in INST_TYPE[alpha|->wordsSyntax.dest_word_type l,beta|->wordsSyntax.dest_word_type r] w2w_def |> translate end) w2ws;
*)

val res = translate (GEN_ALL x64_enc_thm)

val _ = translate (x64_config_def |> gconv)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
