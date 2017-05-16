open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open compiler64ProgTheory
open arm8_targetTheory arm8Theory;
open inliningLib;

val _ = new_theory "arm8Prog"

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

(*
val _ = translate (conv64_RHS integer_wordTheory.WORD_LEi)
val _ = translate (conv64_RHS integer_wordTheory.WORD_LTi)

val _ = register_type``:64 asm_config``
*)

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

val gconv = CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV)
val econv = CONV_RULE wordsLib.WORD_EVAL_CONV

(*
val spec_word_bit1 = word_bit |> ISPEC``foo:word32`` |> SPEC``11n``|> SIMP_RULE std_ss [word_bit_thm] |> CONV_RULE (wordsLib.WORD_CONV)
val spec_word_bit2 = word_bit |> ISPEC``foo:word64`` |> SPEC``31n``|> SIMP_RULE std_ss [word_bit_thm] |> CONV_RULE (wordsLib.WORD_CONV)

val v2w_rw = Q.prove(`
  v2w [P] = if P then 1w else 0w`,
  rw[]>>EVAL_TAC);
*)

val IS_SOME_rw = Q.prove(`
  (if IS_SOME A then B else C) =
    case A of
    SOME v => B
  | NONE => C`,
  Cases_on`A`>>rw[IS_SOME_DEF]);

val v2w_rw = Q.prove(`
  v2w [P] = if P then 1w else 0w`,
  rw[]>>EVAL_TAC);

(* TODO? more Manual rewrites to get rid of MachineCode type*)

val exh_machine_code = Q.prove(`
∀v f.
(case
  case v of
    (N,imms,immr) =>
      ARM8 (f N imms immr)
of
  ARM8 w => g w
| BadCode v3 => h) =
  case v of (N,imms,immr) =>
  g( f N imms immr)`,
  rw[]>>PairCases_on`v`>>rw[])

val LIST_BIND_option = Q.prove(`
  LIST_BIND (case P of NONE => A | SOME v => B v) f =
  case P of NONE => LIST_BIND A f | SOME v => LIST_BIND (B v) f`,
  Cases_on`P`>>rw[]);

val LIST_BIND_pair = Q.prove(`
  LIST_BIND (case P of (l,r) => A l r) f =
  case P of (l,r) => LIST_BIND (A l r) f`,
  Cases_on`P`>>rw[]);

val notw = Q.prove(`
  !a. ~a = (-1w ?? a)`,
  srw_tac[wordsLib.WORD_BIT_EQ_ss][]);

val defaults = [arm8_ast_def,arm8_encode_def,Encode_def,NoOperation_def,arm8_enc_mov_imm_def,e_data_def,EncodeLogicalOp_def,bop_enc_def,e_sf_def,v2w_rw,arm8_encode_fail_def,e_load_store_def,arm8_load_store_ast_def,e_LoadStoreImmediate_def,e_branch_def,asmSemTheory.is_test_def,cmp_cond_def,dfn'Hint_def]

val arm8_enc_thms =
  arm8_enc_def
  |> SIMP_RULE std_ss [FUN_EQ_THM]
  |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss[``:64 asm``])[]
  |> CONJUNCTS
val arm8_enc1 = el 1 arm8_enc_thms
val arm8_enc2 = el 2 arm8_enc_thms
val arm8_enc3 = el 3 arm8_enc_thms
val arm8_enc4 = el 4 arm8_enc_thms
val arm8_enc5 = el 5 arm8_enc_thms
val arm8_enc6 = el 6 arm8_enc_thms

val arm8_enc1s =
  arm8_enc1
  |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss [``:64 inst``]) defaults
  |> CONJUNCTS

val arm8_enc1_1 = el 1 arm8_enc1s |> wc_simp |> we_simp |> gconv
val arm8_enc1_2 = el 2 arm8_enc1s
  |> SIMP_RULE (srw_ss()++LET_ss) ([Q.ISPEC `LIST_BIND` COND_RAND,Ntimes (Q.ISPEC`option_CASE`COND_RAND) 8,Q.ISPEC`MachineCode_CASE`COND_RAND,COND_RATOR,LIST_BIND_APPEND,IS_SOME_rw]@defaults)
  |> SIMP_RULE (srw_ss()) ([option_case_compute,Q.ISPEC`LIST_BIND`COND_RAND,COND_RATOR]@defaults)
  |> SIMP_RULE (srw_ss()) ((GSYM option_case_compute)::exh_machine_code::defaults)
  |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO,notw] |> gconv

val (binop::shift::rest) = el 3 arm8_enc1s |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss [``:64 arith``]) [] |> CONJUNCTS

val (binopreg_aux::binopimm_aux::_) = binop |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss [``:64 reg_imm``]) [FORALL_AND_THM] |> CONJUNCTS |> map (SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss [``:binop``]) [])

val binopreg = binopreg_aux |> CONJUNCTS |> map(fn th => th |> SIMP_RULE (srw_ss()++LET_ss) (defaults) |> wc_simp |> we_simp |> gconv |>SIMP_RULE std_ss [SHIFT_ZERO])

val binopregth = reconstruct_case ``arm8_enc (Inst (Arith (Binop b n n0 (Reg n'))))`` (rand o rator o rator o rator o rand o rand o rand) (map (csethm 2) binopreg)

val binopimm = binopimm_aux |> CONJUNCTS |> map(fn th => th
  |> SIMP_RULE (srw_ss()++LET_ss)
               (Q.ISPEC`LIST_BIND`COND_RAND ::Q.ISPEC`Data_CASE`COND_RAND:: COND_RATOR :: word_mul_def :: defaults)
  |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO])
(*TODO: fix -- avoid MachineCode type*)

val binopimmth = reconstruct_case ``arm8_enc (Inst (Arith (Binop b n n0 (Imm c))))`` (rand o rator o rator o rator o rand o rand o rand) binopimm

val binopth = reconstruct_case ``arm8_enc(Inst (Arith (Binop b n n0 r)))`` (rand o rand o rand o rand) [binopregth,binopimmth]

val shiftths =
  shift
  |> SIMP_RULE(srw_ss()++LET_ss++DatatypeSimps.expand_type_quants_ss[``:shift``])
      (Q.ISPEC`(λ(f,n). P f n)` COND_RAND::
       Q.ISPEC`LIST_BIND`COND_RAND ::
       COND_RATOR ::
      defaults)
  |> SIMP_RULE (srw_ss()++LET_ss) ([LIST_BIND_option,LIST_BIND_pair]@defaults)
  |> CONJUNCTS
  |> map (fn th => th |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO])

val shiftth = reconstruct_case ``arm8_enc(Inst (Arith (Shift s n n0 n1)))``
  (rand o funpow 3 rator o funpow 3 rand) shiftths

val arm8_enc1_3_aux = binopth :: shiftth :: map (fn th => th |> SIMP_RULE (srw_ss()) defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]) rest

val arm8_enc1_3 = reconstruct_case ``arm8_enc (Inst (Arith a))`` (rand o rand o rand) arm8_enc1_3_aux

val arm8_enc1_4_aux = el 4 arm8_enc1s |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss [``:64 addr``,``:memop``]) ((Q.ISPEC`LIST_BIND` COND_RAND)::(Q.ISPEC`(λ(f,n). P f n)` COND_RAND)::COND_RATOR::defaults)
|> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO] |> CONJUNCTS

val arm8_enc1_4 = reconstruct_case ``arm8_enc (Inst (Mem m n a))`` (rand o rand o rand) [reconstruct_case ``arm8_enc (Inst (Mem m n (Addr n' c)))`` (rand o rator o rator o rand o rand) arm8_enc1_4_aux]

val arm8_simp1 = reconstruct_case ``arm8_enc (Inst i)`` (rand o rand) [arm8_enc1_1,arm8_enc1_2,arm8_enc1_3,arm8_enc1_4]

val arm8_simp2 = arm8_enc2 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults |> wc_simp |> we_simp |> gconv

val arm8_enc3_aux = arm8_enc3
  |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss[``:64 reg_imm``])[FORALL_AND_THM]
  |> CONJUNCTS
  |> map (fn th => th
     |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss[``:cmp``])
                  (Q.ISPEC `LIST_BIND` COND_RAND:: COND_RATOR::defaults)
     |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO])

val arm8_enc3_1 = el 1 arm8_enc3_aux
val arm8_enc3_2 = el 2 arm8_enc3_aux

val arm8_enc3_1_th =
  arm8_enc3_1 |> CONJUNCTS
  |> reconstruct_case ``arm8_enc (JumpCmp c n (Reg n') c0)``
     (rand o funpow 3 rator o rand)

val arm8_enc3_2_th =
  arm8_enc3_2 |> CONJUNCTS
  |> reconstruct_case ``arm8_enc (JumpCmp c n (Imm c') c0)``
     (rand o funpow 3 rator o rand)

val arm8_simp3 =
  reconstruct_case ``arm8_enc (JumpCmp c n r c0)`` (rand o rator o rand)
    [arm8_enc3_1_th,arm8_enc3_2_th]

val arm8_simp4 = arm8_enc4 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO,v2w_rw]

val arm8_simp5 = arm8_enc5 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]

val arm8_simp6 = arm8_enc6
  |> SIMP_RULE (srw_ss() ++ LET_ss) (Q.ISPEC`LIST_BIND`COND_RAND :: COND_RATOR ::word_mul_def :: defaults)
  |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]

val arm8_enc_thm = reconstruct_case ``arm8_enc i`` rand [arm8_simp1,arm8_simp2,arm8_simp3,arm8_simp4,arm8_simp5,arm8_simp6]

val ct_curr_def = tDefine "ct_curr" `
  ct_curr b (w:word64) =
     if
       ((1w && w) ≠ 0w ⇔ b) ∨
       if b then w = 0w else w = 0xFFFFFFFFFFFFFFFFw
     then
       0n
     else 1 + ct_curr b (w ⋙ 1)`
  (WF_REL_TAC`measure (w2n o SND)`
  THEN SRW_TAC [] [wordsTheory.LSR_LESS]
  THEN Cases_on `w = 0w`
  THEN FULL_SIMP_TAC (srw_ss()) [wordsTheory.word_0, wordsTheory.LSR_LESS])

val CountTrailing_eq = Q.prove(`
  ∀b w. CountTrailing (b,w) = ct_curr b w`,
  ho_match_mp_tac (fetch "-" "ct_curr_ind")>>
  rpt strip_tac>>
  PURE_REWRITE_TAC[Once ct_curr_def,word_bit_thm]>>
  fs[]>>`-1w:word64 = 0xFFFFFFFFFFFFFFFFw` by fs[]>>
  IF_CASES_TAC
  >-
    (PURE_REWRITE_TAC[Once CountTrailing_def,word_bit_thm]>>
    simp[])
  >>
    simp[Once CountTrailing_def,word_bit_thm]>>
    metis_tac[]);

val res = translate ct_curr_def

fun specv64 v = INST_TYPE [v|->``:64``]
val _ = translate (specv64 ``:'N`` EncodeBitMaskAux_def |> gconv |> SIMP_RULE std_ss [CountTrailing_eq, word_ror_eq_any_word64_ror])

(*TODO, make this translate:
specv64 ``:'M`` DecodeBitMasks_def

INST_TYPE [``:'N``|->``:64``] EncodeBitMask_def |> SIMP_RULE std_ss [notw] |> gconv

val w2ws = mk_set(map type_of ((find_terms (fn t => same_const ``w2w`` t)) (concl arm8_enc_thm)))

val res = map (fn ty => let val (l,r) = dom_rng ty in INST_TYPE[alpha|->wordsSyntax.dest_word_type l,beta|->wordsSyntax.dest_word_type r] w2w_def |> translate end) w2ws;

val res = translate arm8_enc_thm

val res = translate (arm8_config_def |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]|> econv)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = (ml_translatorLib.clean_on_exit := true);
*)
val _ = export_theory();
