(*
  Translate the ARMv8 instruction encoder and ARMv8-specific config.
*)
open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open x64ProgTheory
open arm8_targetTheory arm8Theory;
open inliningLib;

val _ = new_theory "arm8Prog"

val _ = translation_extends "x64Prog";
val _ = ml_translatorLib.use_string_type true;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "arm8Prog");

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
  val def = def |> REWRITE_RULE (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val IS_SOME_rw = Q.prove(`
  (if IS_SOME A then B else C) =
    case A of
    SOME v => B
  | NONE => C`,
  Cases_on`A`>>rw[IS_SOME_DEF]);

val v2w_rw = Q.prove(`
  v2w [P] = if P then 1w else 0w`,
  rw[]>>EVAL_TAC);

(* TODO? more Manual rewrites to get rid of MachineCode type, which probably isn't that expensive *)

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

val defaults = [arm8_ast_def, arm8_encode_def, Encode_def,
  NoOperation_def, arm8_enc_mov_imm_def, e_data_def,
  EncodeLogicalOp_def, bop_enc_def, e_sf_def, v2w_rw,
  arm8_encode_fail_def, e_load_store_def, arm8_load_store_ast_def,
  e_LoadStoreImmediate_def, e_branch_def, asmSemTheory.is_test_def,
  cmp_cond_def, dfn'Hint_def];

val arm8_enc_thms =
  arm8_enc_def
  |> SIMP_RULE std_ss [FUN_EQ_THM]
  |> SIMP_RULE (srw_ss() ++ LET_ss ++
                DatatypeSimps.expand_type_quants_ss[``:64 asm``])[]
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

val arm8_enc1_2 = el 2 arm8_enc1s |> SIMP_RULE (srw_ss()++LET_ss)
  ([Q.ISPEC `LIST_BIND` COND_RAND, Ntimes
  (Q.ISPEC`option_CASE`COND_RAND) 8,
  Q.ISPEC`MachineCode_CASE`COND_RAND, COND_RATOR, LIST_BIND_APPEND,
  IS_SOME_rw]@defaults) |> SIMP_RULE (srw_ss()) ([option_case_compute,
  Q.ISPEC`LIST_BIND`COND_RAND, COND_RATOR]@defaults) |> SIMP_RULE
  (srw_ss()) ((GSYM option_case_compute)::exh_machine_code::defaults)
  |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO,
  notw] |> gconv

val (binop::shift::rest) = el 3 arm8_enc1s |> SIMP_RULE (srw_ss() ++
  DatatypeSimps.expand_type_quants_ss [``:64 arith``]) [] |> CONJUNCTS

val (binopreg_aux::binopimm_aux::_) = binop |> SIMP_RULE (srw_ss() ++
  DatatypeSimps.expand_type_quants_ss [``:64 reg_imm``])
  [FORALL_AND_THM] |> CONJUNCTS |> map (SIMP_RULE (srw_ss() ++ LET_ss
  ++ DatatypeSimps.expand_type_quants_ss [``:binop``]) [])

val binopreg = binopreg_aux |> CONJUNCTS |> map(fn th => th |>
  SIMP_RULE (srw_ss()++LET_ss) (defaults) |> wc_simp |> we_simp |>
  gconv |>SIMP_RULE std_ss [SHIFT_ZERO])

val binopregth = reconstruct_case
  ``arm8_enc (Inst (Arith (Binop b n n0 (Reg n'))))``
  (rand o rator o rator o rator o rand o rand o rand)
  (map (csethm 2) binopreg)

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

val arm8_enc1_3_aux = binopth :: shiftth :: map (fn th => th |>
SIMP_RULE (srw_ss()) defaults |> wc_simp |> we_simp |> gconv |>
SIMP_RULE std_ss [SHIFT_ZERO]) rest

val arm8_enc1_3 = reconstruct_case ``arm8_enc (Inst (Arith a))`` (rand
o rand o rand) arm8_enc1_3_aux

val arm8_enc1_4_aux = el 4 arm8_enc1s |> SIMP_RULE (srw_ss() ++ LET_ss
  ++ DatatypeSimps.expand_type_quants_ss [``:64 addr``,``:memop``])
  ((Q.ISPEC`LIST_BIND` COND_RAND)::(Q.ISPEC`(λ(f,n). P f n)`
  COND_RAND)::COND_RATOR::defaults) |> wc_simp |> we_simp |> gconv |>
  SIMP_RULE std_ss [SHIFT_ZERO,word_mul_def] |> CONJUNCTS

val arm8_enc1_4 = reconstruct_case
  ``arm8_enc (Inst (Mem m n a))``
  (rand o rand o rand) [reconstruct_case
  ``arm8_enc (Inst (Mem m n (Addr n' c)))``
  (rand o rator o rator o rand o rand) arm8_enc1_4_aux]

val arm8_enc1_5 = el 5 arm8_enc1s

val arm8_simp1 = reconstruct_case ``arm8_enc (Inst i)``
  (rand o rand) [arm8_enc1_1,arm8_enc1_2,arm8_enc1_3,arm8_enc1_4,arm8_enc1_5]

val arm8_simp2 = arm8_enc2 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults
  |> wc_simp |> we_simp |> gconv

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

val arm8_simp4 = arm8_enc4 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults
|> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO,v2w_rw]

val arm8_simp5 = arm8_enc5 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults
|> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]

val arm8_simp6 = arm8_enc6 |> SIMP_RULE (srw_ss() ++ LET_ss)
(Q.ISPEC`LIST_BIND`COND_RAND :: COND_RATOR ::word_mul_def :: defaults)
|> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]

val arm8_enc_thm = reconstruct_case ``arm8_enc i`` rand
[arm8_simp1,arm8_simp2,arm8_simp3,arm8_simp4,arm8_simp5,arm8_simp6]

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
  THEN FULL_SIMP_TAC (srw_ss()) [wordsTheory.word_0, wordsTheory.LSR_LESS]);

val CountTrailing_eq = Q.prove(`
  ∀b w. CountTrailing (b,w) = ct_curr b w`,
  ho_match_mp_tac (fetch "-" "ct_curr_ind")>>
  rpt strip_tac>>
  PURE_REWRITE_TAC[Once ct_curr_def,word_bit_test]>>
  fs[]>>`-1w:word64 = 0xFFFFFFFFFFFFFFFFw` by fs[]>>
  IF_CASES_TAC
  >-
    (PURE_REWRITE_TAC[Once CountTrailing_def,word_bit_test]>>
    simp[])
  >>
    simp[Once CountTrailing_def,word_bit_test]>>
    metis_tac[]);

val res = translate ct_curr_def

(* the encoder uses two special functions that need to be hand translated *)
fun specv64 v = INST_TYPE [v|->``:64``]
val _ = translate (specv64 ``:'N`` EncodeBitMaskAux_def |> gconv |>
SIMP_RULE std_ss [CountTrailing_eq, word_ror_eq_any_word64_ror])

val log2_def = Define`
  log2 n =
  if n < 2 then 0n
  else (log2 (n DIV 2)) + 1`

val LOG2_log2 = Q.prove(`
  ∀n. n ≠ 0 ⇒
  log2 n = LOG2 n`,
  ho_match_mp_tac (fetch "-" "log2_ind")>>rw[]>>
  simp[Once log2_def,bitTheory.LOG2_def]>>
  PURE_REWRITE_TAC [Once numeral_bitTheory.LOG_compute]>>
  IF_CASES_TAC>>fs[ADD1,GSYM bitTheory.LOG2_def]>>
  first_assum match_mp_tac>>
  `2 ≤ n` by fs[]>>
  drule bitTheory.DIV_GT0>>
  fs[]);

val hsb_compute = Q.prove(`
  HighestSetBit (w:word7) =
  if w = 0w then -1 else w2i(n2w(log2 (w2n w)):word7)`,
  fs[word_log2_def,HighestSetBit_def]>>IF_CASES_TAC>>fs[]>>
  `w2n w ≠ 0` by fs[]>>
  metis_tac[LOG2_log2]);

val v2w_Ones = Q.prove(`
  (v2w (Ones n)):word6 = n2w (2 ** n -1)`,
  rw[Ones_def]>>
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss][]>>
  rewrite_tac [bitstringTheory.word_index_v2w,word_index_n2w] >>
  simp [bitstringTheory.testbit, listTheory.PAD_LEFT,bitTheory.BIT_EXP_SUB1]>>
  eq_tac>>
  fs[EL_GENLIST]);

val _ = translate bitstringTheory.zero_extend_def
val _ = translate bitstringTheory.fixwidth_def
val _ = translate bitstringTheory.field_def
val _ = translate bitstringTheory.v2n_def

(* TODO: already in lexerProg but not stored *)
val l2n_side = Q.prove(`
  ∀b a. a ≠ 0 ⇒ l2n_side a b`,
  Induct>>
  rw[Once lexerProgTheory.l2n_side_def]) |> update_precondition;

val v2n_side = Q.prove(`
  v2n_side v ⇔ T`,
  EVAL_TAC>>
  fs[l2n_side]) |> update_precondition;

val notw = Q.prove(`
  !a. ~a = (-1w ?? (a))`,
  srw_tac[wordsLib.WORD_BIT_EQ_ss][]);

val res = translate (EVAL``w2v (w:word6)`` |> SIMP_RULE (srw_ss()) [word_bit_test,word_bit_def,word_bit])

val Num_rw = Q.prove(`
  (if len < 1 then NONE
  else
    f (Num len)) =
  if len < 1 then NONE
    else f (Num (ABS len))`,
  rw[]>>
  `0 ≤ len` by intLib.COOPER_TAC>>
  metis_tac[integerTheory.INT_ABS_EQ_ID])

val res = translate (specv64 ``:'M`` DecodeBitMasks_def |> SIMP_RULE
  (srw_ss()++ARITH_ss) [hsb_compute, v2w_Ones, Replicate_def,
  bitstringTheory.length_pad_left, Ones_def, GSYM
  bitstringTheory.n2w_v2n, Num_rw] |> CONV_RULE (wordsLib.WORD_CONV) o
  SIMP_RULE std_ss [word_concat_def, word_join_def, w2w_w2w] |>
  SIMP_RULE std_ss [word_extract_w2w_mask, w2w_id, SHIFT_ZERO, notw,
  word_mul_def] |> gconv)

val decodebitmasks_side = Q.prove(`
  decodebitmasks_side x ⇔ T`,
  PairCases_on`x`>>EVAL_TAC>>fs[] >>
  simp_tac std_ss [GSYM LENGTH_NIL,LENGTH_GENLIST]) |> update_precondition

val res = translate (INST_TYPE [``:'N``|->``:64``] EncodeBitMask_def
 |> SIMP_RULE std_ss [notw] |> gconv)

val res = translate arm8_enc_thm

val _ = translate (valid_immediate_def |> SIMP_RULE bool_ss
[IN_INSERT,NOT_IN_EMPTY]|> econv)

val res = translate (arm8_config_def |> SIMP_RULE bool_ss
[IN_INSERT,NOT_IN_EMPTY]|> econv)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
