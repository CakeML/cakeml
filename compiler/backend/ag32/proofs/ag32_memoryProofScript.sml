(*
  Prove some properties about the ag32 memory layout including
  correctness of the startup code and length and lookup theorems for
  other parts of memory.
*)
open preamble ag32_memoryTheory
local
  open wordsLib blastLib asmLib combinLib ag32_targetLib
  open data_to_word_memoryProofTheory backendProofTheory
       ag32_machine_configTheory
in end

val _ = new_theory"ag32_memoryProof";

(* TODO: move *)

Theorem get_byte_word_of_bytes:
   good_dimindex(:'a) ⇒
   i < LENGTH ls ∧ LENGTH ls ≤ w2n (bytes_in_word:'a word) ⇒
  (get_byte (n2w i) (word_of_bytes be (0w:'a word) ls) be = EL i ls)
Proof
  strip_tac
  \\ `∃k. dimindex(:'a) DIV 8 = 2 ** k` by(
    fs[labPropsTheory.good_dimindex_def]
    \\ TRY(qexists_tac`2` \\ EVAL_TAC \\ NO_TAC)
    \\ TRY(qexists_tac`3` \\ EVAL_TAC \\ NO_TAC) )
  \\ strip_tac
  \\ Q.ISPECL_THEN[`be`,`0w`,`ls`,`2 ** k`]mp_tac word_of_bytes_bytes_to_word
  \\ impl_keep_tac >- (
    rfs[bytes_in_word_def, dimword_def]
    \\ fs[labPropsTheory.good_dimindex_def] \\ rfs[])
  \\ rw[]
  \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_bytes_to_word]
  \\ rw[]
QED

Theorem get_byte_EL_words_of_bytes:
   ∀be ls.
   i < LENGTH ls ∧ w2n (bytes_in_word:'a word) * LENGTH ls ≤ dimword(:'a) ∧ good_dimindex(:'a) ⇒
   (get_byte (n2w i : α word)
      (EL (w2n (byte_align ((n2w i):α word)) DIV (w2n (bytes_in_word:α word)))
        (words_of_bytes be ls)) be = EL i ls)
Proof
  completeInduct_on`i`
  \\ Cases_on`ls`
  \\ rw[words_of_bytes_def]
  \\ qmatch_goalsub_abbrev_tac`MAX 1 bw`
  \\ `0 < bw` by (
     fs[Abbr`bw`,labPropsTheory.good_dimindex_def]
     \\ EVAL_TAC \\ fs[dimword_def] )
  \\ `MAX 1 bw = bw` by rw[MAX_DEF] \\ fs[]
  \\ Cases_on`i < bw` \\ fs[]
  >- (
    `byte_align (n2w i) = 0w`
    by(
      simp[alignmentTheory.byte_align_def]
      \\ irule lt_align_eq_0
      \\ fs[labPropsTheory.good_dimindex_def,Abbr`bw`]
      \\ rfs[bytes_in_word_def,dimword_def] )
    \\ simp[ZERO_DIV]
    \\ DEP_REWRITE_TAC[UNDISCH get_byte_word_of_bytes]
    \\ fs[LENGTH_TAKE_EQ]
    \\ Cases_on`i` \\ fs[EL_TAKE] )
  \\ fs[NOT_LESS]
  \\ pop_assum (strip_assume_tac o SIMP_RULE std_ss [LESS_EQ_EXISTS])
  \\ `byte_align (n2w (bw + p)) = n2w bw + byte_align (n2w p)`
  by (
    simp[GSYM word_add_n2w]
    \\ simp[alignmentTheory.byte_align_def]
    \\ DEP_REWRITE_TAC[align_add_aligned_gen]
    \\ simp[Abbr`bw`]
    \\ CONV_TAC(REWR_CONV(GSYM alignmentTheory.byte_aligned_def))
    \\ (data_to_word_assignProofTheory.byte_aligned_bytes_in_word
        |> Q.GEN`w` |> Q.SPEC`1w` |> UNDISCH |> mp_tac)
    \\ simp[] )
  \\ simp[]
  \\ DEP_REWRITE_TAC[w2n_add]
  \\ conj_tac
  >- (
    simp[Abbr`bw`]
    \\ reverse conj_tac >- (
      fs[labPropsTheory.good_dimindex_def,
         bytes_in_word_def]
      \\ EVAL_TAC \\ fs[] \\ EVAL_TAC )
    \\ simp[alignmentTheory.byte_align_def]
    \\ DEP_REWRITE_TAC[word_msb_align]
    \\ conj_tac >- ( fs[labPropsTheory.good_dimindex_def])
    \\ simp[word_msb_n2w]
    \\ qmatch_assum_abbrev_tac`bw * r ≤ dimword _`
    \\ `r ≤ dimword (:'a) DIV bw` by fs[X_LE_DIV]
    \\ `p < dimword(:'a) DIV bw` by fs[]
    \\ match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP
    \\ fs[dimword_def, bytes_in_word_def]
    \\ fs[Abbr`bw`, labPropsTheory.good_dimindex_def]
    \\ rfs[] )
  \\ `bw < dimword(:'a)` by fs[Abbr`bw`, bytes_in_word_def]
  \\ simp[]
  \\ DEP_REWRITE_TAC[ADD_DIV_RWT]
  \\ simp[]
  \\ simp[EL_CONS,PRE_SUB1]
  \\ simp[GSYM word_add_n2w]
  \\ `n2w bw = byte_align (n2w bw)`
  by(
    fs[Abbr`bw`,bytes_in_word_def,alignmentTheory.byte_align_def]
    \\ fs[labPropsTheory.good_dimindex_def]
    \\ EVAL_TAC \\ fs[dimword_def] \\ EVAL_TAC )
  \\ pop_assum SUBST1_TAC
  \\ once_rewrite_tac[WORD_ADD_COMM]
  \\ simp[data_to_word_memoryProofTheory.get_byte_byte_align]
  \\ first_x_assum(qspec_then`p`mp_tac)
  \\ simp[]
  \\ disch_then(qspecl_then[`be`,`DROP (bw-1)t`]mp_tac)
  \\ impl_tac >- fs[ADD1]
  \\ simp[EL_DROP]
QED

Theorem get_mem_word_get_byte_gen:
   (∀x. r0 + n2w (4 * (LENGTH ll + k)) <=+ x ∧ x <+ r0 + n2w (4 * (LENGTH ll + k) + 4)
      ⇒ (m x = get_byte x (EL (w2n (byte_align x - r0) DIV 4) (ll ++ ls ++ lr)) F)) ∧
   (LENGTH ll = off) ∧
   k < LENGTH ls ∧ byte_aligned r0 ∧ (4 * (off + k)) < dimword(:31) ∧
   w2n r0 + (4 * (off + k) + 4) < dimword(:32)
   ⇒ (get_mem_word m (r0 + n2w (4 * (off + k))) = EL k ls)
Proof
  rw[get_mem_word_def]
  \\ ntac 4 (
    qmatch_goalsub_abbrev_tac`m x`
    \\ first_assum(qspec_then`x`mp_tac)
    \\ impl_tac
    >- (
      fs[Abbr`x`]
      \\ Cases_on`r0` \\ fs[word_add_n2w]
      \\ fs[word_ls_n2w, word_lo_n2w] )
    \\ disch_then SUBST_ALL_TAC
    \\ qunabbrev_tac`x`)
  \\ last_x_assum kall_tac
  \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ `aligned 2 pc`
  by (
    simp[Abbr`pc`]
    \\ (alignmentTheory.aligned_add_sub_cor
        |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
        |> irule)
    \\ simp[]
    \\ simp[GSYM addressTheory.ALIGNED_eq_aligned]
    \\ simp[addressTheory.ALIGNED_n2w])
  \\ simp[align_add_aligned_gen]
  \\ simp[Abbr`pc`]
  \\ qmatch_goalsub_abbrev_tac`r0 + x`
  \\ `align 2 (r0 + x) = r0 + x` by fs[alignmentTheory.aligned_def]
  \\ `r0 + x = byte_align (r0 + x)` by fs[alignmentTheory.byte_align_def]
  \\ qhdtm_x_assum`align`SUBST_ALL_TAC
  \\ simp_tac(srw_ss())[]
  \\ pop_assum SUBST_ALL_TAC
  \\ once_rewrite_tac[WORD_ADD_COMM]
  \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
  \\ DEP_REWRITE_TAC[
       data_to_word_memoryProofTheory.get_byte_byte_align
       |> Q.GEN`a'` |> Q.SPEC`0w` |> SIMP_RULE(srw_ss())[]]
  \\ rewrite_tac[CONJ_ASSOC]
  \\ conj_tac >- EVAL_TAC
  \\ DEP_REWRITE_TAC[w2n_add]
  \\ DEP_REWRITE_TAC[ADD_DIV_RWT]
  \\ conj_tac >- ( simp[Abbr`x`] \\ EVAL_TAC )
  \\ conj_tac >- (
    fs[Abbr`x`, word_msb_n2w_numeric, NOT_LESS_EQUAL]
    \\ EVAL_TAC )
  \\ `w2n x DIV 4 = k + LENGTH ll`
  by (
    simp[Abbr`x`]
    \\ once_rewrite_tac[MULT_COMM]
    \\ simp[MULT_DIV] )
  \\ pop_assum SUBST_ALL_TAC
  \\ ntac 3 (
    qmatch_goalsub_abbrev_tac`w2n a`
    \\ pop_assum mp_tac \\ CONV_TAC(LAND_CONV EVAL)
    \\ strip_tac \\ simp[Abbr`a`] )
  \\ simp[EL_APPEND_EQN]
  \\ simp[get_byte_def, byte_index_def]
  \\ blastLib.BBLAST_TAC
QED

val get_mem_word_get_byte =
  get_mem_word_get_byte_gen
  |> Q.GEN`r0` |> Q.SPEC`0w` |> SIMP_RULE(srw_ss())[EVAL``byte_aligned 0w``]
  |> curry save_thm "get_mem_word_get_byte";

Theorem ag32_enc_lengths:
   LENGTH (ag32_enc istr) ∈ {4;8;12;16}
Proof
  Cases_on`istr`
  \\ TRY(rename1`JumpCmp _ _ ri _` \\ Cases_on`ri`)
  \\ TRY(rename1`Inst i ` \\ Cases_on`i`)
  \\ TRY(rename1`Inst (Mem m _ ri) ` \\ Cases_on`m` \\ Cases_on`ri`)
  \\ TRY(rename1`Inst (Arith a) ` \\ Cases_on`a`)
  \\ TRY(rename1`Inst (Arith (Binop _ _ _ ri)) ` \\ Cases_on`ri`)
  \\  rw[ag32_targetTheory.ag32_enc_def,
         ag32_targetTheory.ag32_constant_def,
         ag32_targetTheory.ag32_jump_constant_def,
         ag32_targetTheory.ag32_encode_def,
         ag32_targetTheory.ag32_encode1_def]
QED

Theorem bytes_in_memory_get_byte_words:
   ∀ls ll a.
   (∀k. k ∈ all_words a (LENGTH ls) ⇒
        (m k = get_byte k (EL (w2n (byte_align k) DIV 4) (ll ++ words_of_bytes be ls ++ lr)) be)) ∧
   (a = n2w (4 * LENGTH ll)) ∧ (all_words a (LENGTH ls) ⊆ md)
   ∧ 4 * (LENGTH ll) < dimword(:31) ∧ 4 * LENGTH ls ≤ dimword(:32)
   ⇒
   bytes_in_memory (a:word32) ls m md
Proof
  rw[]
  \\ irule asmPropsTheory.read_bytearray_IMP_bytes_in_memory
  \\ simp[] \\ fs[SUBSET_DEF]
  \\ qexists_tac`SOME o m`
  \\ simp[]
  \\ irule data_to_word_assignProofTheory.IMP_read_bytearray_GENLIST
  \\ simp[] \\ rw[]
  \\ last_x_assum(qspec_then`n2w i + n2w (4 * LENGTH ll)`mp_tac)
  \\ impl_tac
  >- ( simp[IN_all_words] \\ qexists_tac`i` \\ simp[] )
  \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`byte_align (_ + x)`
  \\ `byte_aligned x` by (
    simp[Abbr`x`]
    \\ simp[alignmentTheory.byte_aligned_def]
    \\ simp[GSYM addressTheory.ALIGNED_eq_aligned]
    \\ simp[addressTheory.ALIGNED_n2w] )
  \\ `byte_align (n2w i + x) = x + byte_align (n2w i)`
  by (
    simp[alignmentTheory.byte_align_def]
    \\ fs[alignmentTheory.byte_aligned_def]
    \\ simp[align_add_aligned_gen] )
  \\ simp[]
  \\ DEP_REWRITE_TAC[w2n_add]
  \\ conj_tac
  >- (
      simp[alignmentTheory.byte_align_def,Abbr`x`]
      \\ simp[alignmentTheory.align_w2n]
      \\ simp[multiwordTheory.d_word_msb]
      \\ DEP_REWRITE_TAC[LESS_MOD]
      \\ fs[NOT_LESS_EQUAL]
      \\ conj_asm2_tac >- fs[]
      \\ irule IMP_MULT_DIV_LESS
      \\ fs[] )
  \\ DEP_REWRITE_TAC[ADD_DIV_RWT]
  \\ qspecl_then[`4`,`LENGTH ll`]mp_tac MULT_DIV
  \\ simp[Abbr`x`] \\ disch_then kall_tac
  \\ rewrite_tac[GSYM APPEND_ASSOC]
  \\ DEP_ONCE_REWRITE_TAC[EL_APPEND2]
  \\ simp[]
  \\ drule (#1(EQ_IMP_RULE byte_align_aligned))
  \\ disch_then (SUBST1_TAC o SYM)
  \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
  \\ conj_tac >- EVAL_TAC
  \\ DEP_REWRITE_TAC[EL_APPEND1]
  \\ conj_tac
  >- (
    simp[alignmentTheory.byte_align_def, alignmentTheory.align_w2n, DIV_LT_X, LENGTH_words_of_bytes, bytes_in_word_def]
    \\ DEP_ONCE_REWRITE_TAC[LESS_MOD]
    \\ simp[LEFT_ADD_DISTRIB]
    \\ `4 * (i DIV 4) ≤ i`
    by (
      once_rewrite_tac[MULT_COMM]
      \\ simp[GSYM X_LE_DIV] )
    \\ fs[]
    \\ simp[DIV_LT_X, LEFT_ADD_DISTRIB]
    \\ qmatch_goalsub_abbrev_tac`i < z`
    \\ `LENGTH ls ≤ z` suffices_by simp[]
    \\ qspec_then`4`mp_tac DIVISION
    \\ simp[]
    \\ disch_then(qspec_then`LENGTH ls`mp_tac)
    \\ disch_then SUBST1_TAC
    \\ simp[Abbr`z`]
    \\ rw[MIN_DEF]
    \\ simp[LESS_OR_EQ] )
  \\ qspecl_then[`be`,`ls`]mp_tac(INST_TYPE[alpha|->``:32``]get_byte_EL_words_of_bytes)
  \\ simp[bytes_in_word_def]
  \\ impl_tac >- EVAL_TAC
  \\ rw[]
QED

val get_byte_repl = Q.prove(`
  n+m < dimword(:32) ∧
  (m MOD 4 = 0n) ==>
  (get_byte ((n2w (n + m)):word32) w F =
  get_byte (n2w n) w F)`,
  EVAL_TAC>>
  fs[]>>rw[]>>
  ntac 2 AP_TERM_TAC>>
  intLib.ARITH_TAC);

(* -- *)

Theorem byte_aligned_code_start_offset:
   byte_aligned (n2w(code_start_offset num_ffis) : word32)
Proof
  rw[code_start_offset_def]
  \\ `ffi_offset = 4 * w2n (bytes_in_word:word32)` by EVAL_TAC
  \\ pop_assum SUBST1_TAC
  \\ simp[GSYM word_add_n2w]
  \\ qmatch_goalsub_abbrev_tac`byte_aligned (a + _)`
  \\ Q.ISPECL_THEN[`a`,`4 * (num_ffis + 2)`]mp_tac(Q.GENL[`a`,`i`]backendProofTheory.byte_aligned_mult)
  \\ impl_tac >- EVAL_TAC
  \\ simp[GSYM word_add_n2w, GSYM word_mul_n2w]
  \\ rw[Abbr`a`]
  \\ EVAL_TAC
QED

Theorem LENGTH_startup_code:
    LENGTH (startup_code f c d) ≤ startup_code_size
Proof
  simp[startup_code_def,LENGTH_FLAT,SUM_MAP_K,MAP_MAP_o,o_DEF]>>
  `15*16 ≤ startup_code_size` by EVAL_TAC>>
  match_mp_tac LESS_EQ_TRANS>>
  HINT_EXISTS_TAC>>
  qmatch_goalsub_abbrev_tac`_ n cl bl`>>
  CONJ_TAC>- (
    PURE_REWRITE_TAC[GSYM (LENGTH_startup_asm_code)]>>
    match_mp_tac SUM_MAP_BOUND>>
    rw[]>>qspec_then`x`mp_tac (Q.GEN`istr`ag32_enc_lengths)>>
    rw[]>>fs[]) >>
  simp[]
QED

Theorem LENGTH_ag32_enc_MOD_4:
   LENGTH (ag32_enc i) MOD 4 = 0
Proof
  qspec_then`i`mp_tac(Q.GEN`istr`ag32_enc_lengths)
  \\ rw[] \\ rw[]
QED

Theorem LENGTH_startup_code_MOD_4:
    LENGTH (startup_code f c d) MOD 4 = 0
Proof
  simp[startup_code_def,LENGTH_FLAT,SUM_MAP_K,MAP_MAP_o,o_DEF]>>
  DEP_ONCE_REWRITE_TAC [SUM_MOD]>>
  simp[MAP_MAP_o,o_DEF]>>
  qmatch_goalsub_abbrev_tac`MAP ff _`>>
  `ff = λx. 0n` by
    (fs[Abbr`ff`,FUN_EQ_THM]>>
    rw[]>>qspec_then`x`mp_tac (Q.GEN`istr`ag32_enc_lengths)>>
    rw[]>>fs[])>>
  simp[Q.ISPEC`λx. 0n`SUM_MAP_K  |> SIMP_RULE (srw_ss())[]]
QED

val sz = (rconc (EVAL``LENGTH ag32_ffi_code + cline_size DIV 4 + stdin_size DIV 4 + heap_size DIV 4 + startup_code_size DIV 4 + (output_buffer_size + 16) DIV 4 + 3``));

Theorem LENGTH_init_memory_words:
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧ LENGTH inp ≤ stdin_size ⇒
   (LENGTH (init_memory_words c d f cl inp) =
   LENGTH d +
   LENGTH (ag32_ffi_jumps f) +
   LENGTH c DIV 4 + MIN 1 (LENGTH c MOD 4) +
   ^(sz))
Proof
(* adjust as necessary *)
  simp[init_memory_words_def] >>
  strip_tac>>
  simp[LENGTH_ag32_ffi_code]>>
  qmatch_goalsub_abbrev_tac`codel + (cll + (stl + (scl+ (_ + (_ + (scpad + _)) ))))`>>
  fs[LENGTH_words_of_bytes, bitstringTheory.length_pad_right,
          bytes_in_word_def, LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS,
          Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]>>
  `cll = cline_size DIV 4` by
     (simp[Abbr`cll`]>>
     qmatch_goalsub_abbrev_tac`clll DIV 4`>>
     `clll = cline_size` by
       (unabbrev_all_tac>>fs[])>>
     simp[cline_size_def])>>
  `stl = stdin_size DIV 4` by
     (simp[Abbr`stl`]>>
     qmatch_goalsub_abbrev_tac`stll DIV 4`>>
     `stll = stdin_size` by
       (unabbrev_all_tac>>fs[])>>
     simp[stdin_size_def])>>
  `scl + scpad = startup_code_size DIV 4` by
    (unabbrev_all_tac>>fs[LENGTH_startup_code_MOD_4]>>
    qmatch_goalsub_abbrev_tac`A DIV 4 + _`>>
    DEP_REWRITE_TAC[GSYM (Q.SPEC `4n` ADD_DIV_RWT|>SIMP_RULE (srw_ss())[])]>>
    unabbrev_all_tac>>simp[LENGTH_startup_code_MOD_4]>>
    AP_THM_TAC>>AP_TERM_TAC>>
    match_mp_tac (DECIDE``a ≤ b ⇒ (a+(b-a) = b:num)``)>>
    simp[LENGTH_startup_code])>>
  pop_assum mp_tac>>simp[]>>EVAL_TAC>>
  simp[Abbr`codel`]
QED

val lem = Q.prove(`
  (m MOD 4 = 0) ∧ n < m ⇒ n DIV 4 < m DIV 4`,
  intLib.ARITH_TAC);

Theorem init_memory_startup:
   ∀code data ffis n.
   n < LENGTH (startup_code (LENGTH ffis) (LENGTH code) (LENGTH data)) ⇒
   (init_memory code data ffis inputs (n2w n) = EL n (startup_code (LENGTH ffis) (LENGTH code) (LENGTH data)))
Proof
  Cases_on`inputs`
  \\ ntac 5 strip_tac
  \\ simp[init_memory_def]
  \\ qmatch_goalsub_abbrev_tac`EL n sc`
  \\ Q.ISPECL_THEN[`n`,`F`,`sc`]mp_tac
       (Q.GEN`i`(INST_TYPE[alpha|->``:32``]get_byte_EL_words_of_bytes))
  \\ simp[init_memory_words_def,Abbr`sc`]
  \\ simp[bytes_in_word_def]
  \\ qmatch_asmsub_rename_tac`_ f c d`
  \\ assume_tac LENGTH_startup_code
  \\ fs[startup_code_size_def]
  \\ impl_tac >- (
    fs[startup_code_size_def]>>
    EVAL_TAC)
  \\ simp[alignmentTheory.byte_align_def]
  \\ rewrite_tac[GSYM APPEND_ASSOC]
  \\ DEP_REWRITE_TAC [EL_APPEND1]
  \\ simp[LENGTH_words_of_bytes,bytes_in_word_def,LENGTH_startup_code_MOD_4]
  \\ rveq
  \\ fs[DIV_LT_X]
  \\ fs[alignmentTheory.align_w2n]
  \\ DEP_REWRITE_TAC[LESS_MOD]
  \\ fs[]
  \\ conj_tac
  >- (
    irule IMP_MULT_DIV_LESS
    \\ fs[] )
  >>
    match_mp_tac lem>>
    fs[LENGTH_startup_code_MOD_4]
QED

Theorem init_memory_code:
   ∀code data ffis n.
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧ LENGTH inp ≤ stdin_size ∧
   code_start_offset (LENGTH ffis) + (LENGTH code) + 4 * LENGTH data < memory_size  ∧
   n < LENGTH code ⇒
   (init_memory code data ffis (cl,inp) (n2w n + n2w (code_start_offset (LENGTH ffis))) = EL n code)
Proof
  ntac 5 strip_tac
  \\ simp[init_memory_def]
  \\ simp[word_add_n2w]
  \\ simp[init_memory_words_def] >>
  qmatch_goalsub_abbrev_tac `hh ++ cc ++d`>>
  `LENGTH hh = LENGTH (ag32_ffi_jumps ffis) + ^(sz)` by
    (fs[Abbr`hh`]>>
    simp[LENGTH_ag32_ffi_code,LENGTH_ag32_ffi_jumps]>>
    qmatch_goalsub_abbrev_tac`(cll + (stl + (scl+ (_ + (_ + (_ +(scpad + _)) )))))`>>
    fs[LENGTH_words_of_bytes, bitstringTheory.length_pad_right,
            bytes_in_word_def, LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS,
            Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]>>
    `cll = cline_size DIV 4` by
       (simp[Abbr`cll`]>>
       qmatch_goalsub_abbrev_tac`clll DIV 4`>>
       `clll = cline_size` by
         (unabbrev_all_tac>>fs[])>>
       simp[cline_size_def])>>
    `stl = stdin_size DIV 4` by
       (simp[Abbr`stl`]>>
       qmatch_goalsub_abbrev_tac`stll DIV 4`>>
       `stll = stdin_size` by
         (unabbrev_all_tac>>fs[])>>
       simp[stdin_size_def])>>
    `scl +scpad = startup_code_size DIV 4` by
      (unabbrev_all_tac>>fs[LENGTH_startup_code_MOD_4]>>
      qmatch_goalsub_abbrev_tac`A DIV 4 + _`>>
      DEP_REWRITE_TAC[GSYM (Q.SPEC `4n` ADD_DIV_RWT|>SIMP_RULE (srw_ss())[])]>>
      unabbrev_all_tac>>simp[LENGTH_startup_code_MOD_4]>>
      AP_THM_TAC>>AP_TERM_TAC>>
      match_mp_tac (DECIDE``a ≤ b ⇒ (a+(b-a) = b:num)``)>>
      simp[LENGTH_startup_code])>>
    pop_assum mp_tac>>simp[]>>EVAL_TAC>>
    fs[])>>
  DEP_ONCE_REWRITE_TAC [EL_APPEND1]>>
  CONJ_TAC>- (
    fs[alignmentTheory.byte_align_def,alignmentTheory.align_w2n,EVAL``code_start_offset f``]>>
    simp[LENGTH_ag32_ffi_jumps]>>
    simp[Abbr`cc`,LENGTH_words_of_bytes,bytes_in_word_def]>>
    intLib.ARITH_TAC)>>
  DEP_ONCE_REWRITE_TAC [EL_APPEND2]>>
  CONJ_TAC>-
    (fs[alignmentTheory.byte_align_def,alignmentTheory.align_w2n,EVAL``code_start_offset f``,LENGTH_ag32_ffi_jumps]>>
    fs[memory_size_def]>>
    intLib.ARITH_TAC)>>
  simp[Abbr`cc`]>>
  simp[LENGTH_ag32_ffi_jumps]>>
  qmatch_goalsub_abbrev_tac`EL mm _`>>
  `mm = n DIV 4` by
    (fs[Abbr`mm`,memory_size_def]>>
    fs[alignmentTheory.byte_align_def,alignmentTheory.align_w2n,EVAL``code_start_offset f``]>>
    intLib.ARITH_TAC)>>
  simp[]>>
  `n DIV 4 =  w2n (byte_align ((n2w n):word32)) DIV 4` by
    (fs[alignmentTheory.byte_align_def,alignmentTheory.align_w2n,EVAL``code_start_offset f``]>>
    fs[memory_size_def]>>
    intLib.ARITH_TAC)>>
  simp[]>>
  DEP_REWRITE_TAC [get_byte_repl]>>
  CONJ_TAC >- (
    fs[EVAL``code_start_offset f``]>>
    fs[memory_size_def])>>
  DEP_REWRITE_TAC [get_byte_EL_words_of_bytes |> INST_TYPE [alpha|->``:32``] |> SIMP_RULE (srw_ss()) [bytes_in_word_def]]>>
  EVAL_TAC>>fs[memory_size_def]
QED

(* TODO - clean it up a bit (it repeats a lot) *)
Theorem init_memory_data:
   SUM (MAP strlen cl) + LENGTH cl <= cline_size /\
   LENGTH inp <= stdin_size /\
   code_start_offset (LENGTH ffis) + (LENGTH code) +
     4 * LENGTH data < memory_size /\
   (low = code_start_offset (LENGTH ffis) + LENGTH code) /\
   k < LENGTH data /\
   byte_aligned (n2w (LENGTH code):word32)
   ==>
   word_of_bytes F 0w
     [init_memory code data ffis (cl,inp) (n2w (4 * (k + low DIV 4)));
      init_memory code data ffis (cl,inp) (n2w (4 * (k + low DIV 4)) + 1w);
      init_memory code data ffis (cl,inp) (n2w (4 * (k + low DIV 4)) + 2w);
      init_memory code data ffis (cl,inp) (n2w (4 * (k + low DIV 4)) + 3w)] =
    EL k data
Proof
  rw []
  \\ qabbrev_tac `low = LENGTH code + code_start_offset (LENGTH ffis)`
  \\ simp [init_memory_def]
  \\ simp [word_add_n2w]
  \\ simp [init_memory_words_def]
  \\ qmatch_goalsub_abbrev_tac `hh ++ cc ++ d`
  \\ `LENGTH hh = LENGTH (ag32_ffi_jumps ffis) + ^(sz)`
    by (fs[Abbr`hh`]
        \\ simp [LENGTH_ag32_ffi_code, LENGTH_ag32_ffi_jumps]
        \\ qmatch_goalsub_abbrev_tac
          `(cll + (stl + (scl + (_ + (_ + (_ + (scpad + _)))))))`
        \\ fs [LENGTH_words_of_bytes, bitstringTheory.length_pad_right,
               bytes_in_word_def, LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1,
               SUM_MAP_PLUS,
               Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
        \\ `cll = cline_size DIV 4`
          by (simp [Abbr `cll`]
              \\ qmatch_goalsub_abbrev_tac `clll DIV 4`
              \\ `clll = cline_size` by (unabbrev_all_tac \\ fs [])
              \\ simp [cline_size_def])
        \\ `stl = stdin_size DIV 4`
          by (simp [Abbr `stl`]
              \\ qmatch_goalsub_abbrev_tac `stll DIV 4`
              \\ `stll = stdin_size` by (unabbrev_all_tac \\ fs [])
              \\ simp [stdin_size_def])
        \\ `scl + scpad = startup_code_size DIV 4`
          by (unabbrev_all_tac \\ fs [LENGTH_startup_code_MOD_4]
              \\ qmatch_goalsub_abbrev_tac `A DIV 4 + _`
              \\ DEP_REWRITE_TAC
                [GSYM (Q.SPEC `4n` ADD_DIV_RWT|>SIMP_RULE (srw_ss())[])]
              \\ unabbrev_all_tac \\ simp [LENGTH_startup_code_MOD_4]
              \\ AP_THM_TAC \\ AP_TERM_TAC
              \\ match_mp_tac (DECIDE ``a ≤ b ⇒ (a+(b-a) = b:num)``)
              \\ simp [LENGTH_startup_code])
        \\ pop_assum mp_tac \\ simp [] \\ EVAL_TAC
        \\ fs [])
  (* TODO this needs to be moved to this theory *)
  \\ `byte_aligned (n2w (code_start_offset (LENGTH ffis)) : word32)`
      by fs [byte_aligned_code_start_offset]
  (* TODO this was not nice *)
  \\ ntac 4
    (DEP_ONCE_REWRITE_TAC [EL_APPEND2] THEN
       (conj_tac THEN1
         (fs [Abbr `low`, Abbr `cc`, memory_size_def,
              EVAL ``code_start_offset f``,
              alignmentTheory.byte_align_def,
              alignmentTheory.align_w2n,
              LENGTH_ag32_ffi_jumps,
              alignmentTheory.byte_aligned_def,
              GSYM addressTheory.ALIGNED_eq_aligned,
              addressTheory.ALIGNED_n2w,
              LENGTH_words_of_bytes, bytes_in_word_def]
          \\ intLib.ARITH_TAC)))
  \\ simp [word_of_bytes_def, Abbr `cc`, LENGTH_ag32_ffi_jumps]
  (* TODO this is a useful lemma *)
  \\ `!(y:word32) x. get_byte (n2w (4 * x) + y) = get_byte y`
    by (
      rw[FUN_EQ_THM]
      \\ `byte_aligned ((n2w (4 * x)):word32)` by (
        fs[alignmentTheory.byte_aligned_def,
           GSYM addressTheory.ALIGNED_eq_aligned,
           addressTheory.ALIGNED_n2w] )
      \\ `n2w (4 * x) : word32 = byte_align (n2w (4 * x))`
      by ( fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def, alignmentTheory.aligned_def] )
      \\ pop_assum SUBST1_TAC
      \\ match_mp_tac data_to_word_memoryProofTheory.get_byte_byte_align
      \\ EVAL_TAC )
  \\ simp [GSYM word_add_n2w]
  \\ pop_assum (qspec_then `0w` mp_tac) \\ fs []
  \\ disch_then kall_tac
  (* TODO this repeats *)
  \\ qmatch_goalsub_abbrev_tac `EL n _`
  \\ `n = k` by
         (fs [Abbr `low`, Abbr `n`, memory_size_def,
              EVAL ``code_start_offset f``,
              alignmentTheory.byte_align_def,
              alignmentTheory.align_w2n,
              LENGTH_ag32_ffi_jumps,
              alignmentTheory.byte_aligned_def,
              GSYM addressTheory.ALIGNED_eq_aligned,
              addressTheory.ALIGNED_n2w,
              LENGTH_words_of_bytes, bytes_in_word_def]
          \\ intLib.ARITH_TAC)
  \\ pop_assum (SUBST_ALL_TAC)
  \\ qmatch_goalsub_abbrev_tac `get_byte 1w (EL n _)`
  \\ `n = k` by
         (fs [Abbr `low`, Abbr `n`, Abbr `k`, memory_size_def,
              EVAL ``code_start_offset f``,
              alignmentTheory.byte_align_def,
              alignmentTheory.align_w2n,
              LENGTH_ag32_ffi_jumps,
              alignmentTheory.byte_aligned_def,
              GSYM addressTheory.ALIGNED_eq_aligned,
              addressTheory.ALIGNED_n2w,
              LENGTH_words_of_bytes, bytes_in_word_def]
          \\ fs [word_add_n2w, word_mul_n2w]
          \\ intLib.ARITH_TAC)
  \\ pop_assum (SUBST_ALL_TAC)
  \\ qmatch_goalsub_abbrev_tac `get_byte 2w (EL n _)`
  \\ `n = k` by
         (fs [Abbr `low`, Abbr `n`, Abbr `k`, memory_size_def,
              EVAL ``code_start_offset f``,
              alignmentTheory.byte_align_def,
              alignmentTheory.align_w2n,
              LENGTH_ag32_ffi_jumps,
              alignmentTheory.byte_aligned_def,
              GSYM addressTheory.ALIGNED_eq_aligned,
              addressTheory.ALIGNED_n2w,
              LENGTH_words_of_bytes, bytes_in_word_def]
          \\ fs [word_add_n2w, word_mul_n2w]
          \\ intLib.ARITH_TAC)
  \\ pop_assum (SUBST_ALL_TAC)
  \\ qmatch_goalsub_abbrev_tac `get_byte 3w (EL n _)`
  \\ `n = k` by
         (fs [Abbr `low`, Abbr `n`, Abbr `k`, memory_size_def,
              EVAL ``code_start_offset f``,
              alignmentTheory.byte_align_def,
              alignmentTheory.align_w2n,
              LENGTH_ag32_ffi_jumps,
              alignmentTheory.byte_aligned_def,
              GSYM addressTheory.ALIGNED_eq_aligned,
              addressTheory.ALIGNED_n2w,
              LENGTH_words_of_bytes, bytes_in_word_def]
          \\ fs [word_add_n2w, word_mul_n2w]
          \\ intLib.ARITH_TAC)
  \\ pop_assum (SUBST_ALL_TAC)
  \\ simp[set_byte_def,get_byte_def,byte_index_def,word_slice_alt_def]
  \\ blastLib.FULL_BBLAST_TAC
QED

Theorem init_memory_halt:
   (pc = n2w (ffi_jumps_offset + (LENGTH f + 1) * ffi_offset)) ∧
   LENGTH f ≤ LENGTH FFI_codes ∧
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧ LENGTH inp ≤ stdin_size
  ⇒
  (get_mem_word (init_memory c d f (cl,inp)) pc =
    Encode (Jump (fAdd, 0w, Imm 0w)))
Proof
  simp[FFI_codes_def]
  \\ strip_tac
  \\ qpat_x_assum`pc = _`(assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
  \\ qspecl_then[`c`,`d`,`f`,`cl`,`inp`]mp_tac init_memory_words_def
  \\ simp[]
  \\ rewrite_tac[GSYM APPEND_ASSOC, ag32_ffi_jumps_def]
  \\ qmatch_goalsub_abbrev_tac`ls ++ (words_of_bytes F c ++ _)`
  \\ qmatch_goalsub_abbrev_tac`ls ++ lr`
  \\ rewrite_tac[APPEND_ASSOC]
  \\ qmatch_goalsub_abbrev_tac`ll ++ ls ++ lr`
  \\ strip_tac
  \\ qspecl_then[`init_memory c d f (cl,inp)`,`0`]mp_tac(Q.GENL[`m`,`k`,`off`]get_mem_word_get_byte)
  \\ simp[]
  \\ `4 * LENGTH ll = w2n pc`
  by (
    simp[Abbr`ll`,LENGTH_ag32_ffi_code,ccache_jump_ag32_code_def]>>
    qmatch_goalsub_abbrev_tac`_ + (cll + (stl + (scl+ (_ + (_ + (scpad + _)) ))))`>>
    fs[LENGTH_words_of_bytes, bitstringTheory.length_pad_right,
            bytes_in_word_def, LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS,
            Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]>>
    `cll = cline_size DIV 4` by
       (simp[Abbr`cll`]>>
       qmatch_goalsub_abbrev_tac`clll DIV 4`>>
       `clll = cline_size` by
         (unabbrev_all_tac>>fs[])>>
       simp[cline_size_def])>>
    `stl = stdin_size DIV 4` by
       (simp[Abbr`stl`]>>
       qmatch_goalsub_abbrev_tac`stll DIV 4`>>
       `stll = stdin_size` by
         (unabbrev_all_tac>>fs[])>>
       simp[stdin_size_def])>>
    `scl + scpad = startup_code_size DIV 4` by
      (unabbrev_all_tac>>fs[LENGTH_startup_code_MOD_4]>>
      qmatch_goalsub_abbrev_tac`A DIV 4 + _`>>
      DEP_REWRITE_TAC[GSYM (Q.SPEC `4n` ADD_DIV_RWT|>SIMP_RULE (srw_ss())[])]>>
      unabbrev_all_tac>>simp[LENGTH_startup_code_MOD_4]>>
      AP_THM_TAC>>AP_TERM_TAC>>
      match_mp_tac (DECIDE``a ≤ b ⇒ (a+(b-a) = b:num)``)>>
      simp[LENGTH_startup_code])>>
    pop_assum mp_tac>>simp[]>>
    simp[MAP_REVERSE,SUM_REVERSE,Abbr`pc`]>>
    simp[mk_jump_ag32_code_def,Q.ISPEC`λx. 4n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]>>
    EVAL_TAC>>rfs[])
  \\ impl_tac
  >- (
    simp[init_memory_def, Abbr`ls`]
    \\ EVAL_TAC
    \\ reverse conj_asm1_tac
    >- decide_tac
    \\ simp[Abbr`pc`]
    \\ EVAL_TAC
    \\ simp[] )
  \\ simp[Abbr`ls`, halt_jump_ag32_code_def]
QED

Theorem init_memory_ccache:
   (pc = n2w (ffi_jumps_offset + (LENGTH f + 0) * ffi_offset)) ∧
   LENGTH f ≤ LENGTH FFI_codes ∧
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧ LENGTH inp ≤ stdin_size
  ⇒
   (get_mem_word (init_memory c d f (cl,inp)) pc =
    Encode (Jump (fSnd, 0w, Reg 0w)))
Proof
  simp[FFI_codes_def]
  \\ strip_tac
  \\ qpat_x_assum`pc = _`(assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
  \\ qspecl_then[`c`,`d`,`f`,`cl`,`inp`]mp_tac init_memory_words_def
  \\ simp[]
  \\ rewrite_tac[GSYM APPEND_ASSOC, ag32_ffi_jumps_def]
  \\ qmatch_goalsub_abbrev_tac`ls ++ (halt_jump_ag32_code ++ _)`
  \\ qmatch_goalsub_abbrev_tac`ls ++ lr`
  \\ rewrite_tac[APPEND_ASSOC]
  \\ qmatch_goalsub_abbrev_tac`ll ++ ls ++ lr`
  \\ strip_tac
  \\ qspecl_then[`init_memory c d f (cl,inp)`,`0`]mp_tac(Q.GENL[`m`,`k`,`off`]get_mem_word_get_byte)
  \\ simp[]
  \\ `4 * LENGTH ll = w2n pc`
  by (
    simp[Abbr`ll`,LENGTH_ag32_ffi_code,ccache_jump_ag32_code_def]>>
    qmatch_goalsub_abbrev_tac`_ + (cll + (stl + (scl+ (_ + (_ + (scpad + _)) ))))`>>
    fs[LENGTH_words_of_bytes, bitstringTheory.length_pad_right,
            bytes_in_word_def, LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS,
            Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]>>
    `cll = cline_size DIV 4` by
       (simp[Abbr`cll`]>>
       qmatch_goalsub_abbrev_tac`clll DIV 4`>>
       `clll = cline_size` by
         (unabbrev_all_tac>>fs[])>>
       simp[cline_size_def])>>
    `stl = stdin_size DIV 4` by
       (simp[Abbr`stl`]>>
       qmatch_goalsub_abbrev_tac`stll DIV 4`>>
       `stll = stdin_size` by
         (unabbrev_all_tac>>fs[])>>
       simp[stdin_size_def])>>
    `scl + scpad = startup_code_size DIV 4` by
      (unabbrev_all_tac>>fs[LENGTH_startup_code_MOD_4]>>
      qmatch_goalsub_abbrev_tac`A DIV 4 + _`>>
      DEP_REWRITE_TAC[GSYM (Q.SPEC `4n` ADD_DIV_RWT|>SIMP_RULE (srw_ss())[])]>>
      unabbrev_all_tac>>simp[LENGTH_startup_code_MOD_4]>>
      AP_THM_TAC>>AP_TERM_TAC>>
      match_mp_tac (DECIDE``a ≤ b ⇒ (a+(b-a) = b:num)``)>>
      simp[LENGTH_startup_code])>>
    pop_assum mp_tac>>simp[]>>
    simp[MAP_REVERSE,SUM_REVERSE,Abbr`pc`]>>
    simp[mk_jump_ag32_code_def,Q.ISPEC`λx. 4n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]>>
    EVAL_TAC>>rfs[])
  \\ impl_tac
  >- (
    simp[init_memory_def, Abbr`ls`]
    \\ EVAL_TAC
    \\ reverse conj_asm1_tac
    >- decide_tac
    \\ simp[Abbr`pc`]
    \\ EVAL_TAC
    \\ simp[] )
  \\ simp[Abbr`ls`, ccache_jump_ag32_code_def]
QED

Theorem init_memory_startup_bytes_in_memory:
   i < LENGTH sc  ∧
   (sc = startup_asm_code (LENGTH ffis) (n2w (LENGTH code)) (n2w (4 * (LENGTH data)))) ⇒
   bytes_in_memory (n2w (SUM (MAP (LENGTH o ag32_enc) (TAKE i sc)))) (ag32_enc (EL i sc))
     (init_memory code data ffis inputs) ag32_startup_addresses
Proof
  rw[]
  \\ qmatch_asmsub_abbrev_tac`i < LENGTH sc`
  \\ qmatch_goalsub_abbrev_tac`bytes_in_memory a _ m`
  \\ `∃ll lr.
        (init_memory_words code data ffis (FST inputs) (SND inputs) = ll ++ words_of_bytes F (ag32_enc (EL i sc)) ++ lr) ∧
        (n2w (4 * LENGTH ll) = a) ∧
        (4 * LENGTH ll < dimword(:31))`
  by (
    simp[init_memory_words_def, startup_code_def]
    \\ `MAP ag32_enc sc = MAP ag32_enc (TAKE i sc ++ [EL i sc] ++ DROP (i+1) sc)`
    by (
      AP_TERM_TAC
      \\ rewrite_tac[GSYM CONS_APPEND, GSYM APPEND_ASSOC]
      \\ DEP_REWRITE_TAC[GSYM DROP_EL_CONS]
      \\ simp[] )
    \\ pop_assum SUBST_ALL_TAC
    \\ simp[]
    \\ DEP_REWRITE_TAC[words_of_bytes_append]
    \\ conj_tac
    >- (
      simp[bytes_in_word_def]
      \\ DEP_ONCE_REWRITE_TAC[GSYM MOD_PLUS]
      \\ conj_tac >- rw[]
      \\ rewrite_tac[LENGTH_FLAT, MAP_MAP_o]
      \\ DEP_ONCE_REWRITE_TAC[SUM_MOD]
      \\ conj_tac >- rw[]
      \\ rewrite_tac[MAP_MAP_o]
      \\ simp[LENGTH_ag32_enc_MOD_4, o_DEF]
      \\ simp[Q.ISPEC`λx. 0n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]] )
    \\ rewrite_tac[GSYM APPEND_ASSOC]
    \\ qmatch_goalsub_abbrev_tac`ll ++ _`
    \\ qexists_tac`ll`
    \\ simp[]
    \\ simp[Abbr`ll`, Abbr`a`]
    \\ simp[LENGTH_words_of_bytes]
    \\ simp[LENGTH_FLAT, MAP_MAP_o, bytes_in_word_def]
    \\ qmatch_goalsub_abbrev_tac`_ + z`
    \\ `z = 0`
    by (
      simp[Abbr`z`]
      \\ DEP_ONCE_REWRITE_TAC[SUM_MOD]
      \\ simp[MAP_MAP_o, o_DEF, LENGTH_ag32_enc_MOD_4]
      \\ simp[Q.ISPEC`λx. 0n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]  )
    \\ simp[]
    \\ fs[Abbr`z`]
    \\ fs[MOD_EQ_0_DIVISOR]
    \\ `4 * d = d * 4` by simp[]
    \\ pop_assum SUBST_ALL_TAC
    \\ simp[MULT_DIV]
    \\ fs[Abbr`sc`, LENGTH_startup_asm_code]
    \\ qmatch_asmsub_abbrev_tac`SUM (MAP f ls)`
    \\ `SUM (MAP f ls) ≤ LENGTH ls * 16`
    by (
      irule SUM_MAP_BOUND
      \\ simp[Abbr`f`]
      \\ qx_gen_tac `istr`
      \\ mp_tac ag32_enc_lengths
      \\ rw[] )
    \\ fs[Abbr`ls`, LENGTH_startup_asm_code, LENGTH_TAKE_EQ])
  \\ irule bytes_in_memory_get_byte_words
  \\ simp[Abbr`m`]
  \\ Cases_on`inputs`
  \\ simp[init_memory_def]
  \\ fs[PULL_EXISTS]
  \\ map_every qexists_tac[`F`,`ll`,`lr`]
  \\ simp[]
  \\ conj_tac
  >- (
    qspec_then`EL i sc`mp_tac(Q.GEN`istr`ag32_enc_lengths)
    \\ rw[] )
  \\ simp[SUBSET_DEF, IN_all_words, PULL_EXISTS]
  \\ simp[Abbr`a`, word_add_n2w]
  \\ qx_gen_tac`j` \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`SUM (MAP f ls)`
  \\ `SUM (MAP f ls) ≤ LENGTH ls * 16`
  by (
    irule SUM_MAP_BOUND
    \\ simp[Abbr`f`]
    \\ qx_gen_tac `istr`
    \\ mp_tac ag32_enc_lengths
    \\ rw[] )
  \\ `j < 16`
  by (
    qspec_then`EL i sc`mp_tac(Q.GEN`istr`ag32_enc_lengths)
    \\ rw[] \\ fs[] )
  \\ simp[ag32_machine_configTheory.ag32_startup_addresses_def,
          word_ls_n2w, word_lo_n2w]
  \\ simp[EVAL``heap_start_offset``, EVAL``startup_code_size``]
  \\ fs[Abbr`ls`, LENGTH_TAKE_EQ] \\ rfs[]
  \\ fs[Abbr`sc`, LENGTH_startup_asm_code]
QED

val init_asm_state_def = Define`
  init_asm_state code data ffis input =
  let im =  init_memory code data ffis in
  let sac = startup_asm_code (LENGTH ffis) (n2w (LENGTH code)) (n2w (4 * LENGTH data)) in
    FOLDL (λs i. asm i (s.pc + n2w (LENGTH (ag32_enc i))) s)
      (ag32_init_asm_state
        (im input)
        (ag32_startup_addresses))
        sac`;

val (asm_tm, mk_asm, dest_asm, is_asm) = HolKernel.syntax_fns3 "asmSem" "asm"
val (asm_ok_tm, mk_asm_ok, dest_asm_ok, is_asm_ok) = HolKernel.syntax_fns2 "asm" "asm_ok"
val (ag32_enc_tm, mk_ag32_enc, dest_ag32_enc, is_ag32_enc) = HolKernel.syntax_fns1 "ag32_target" "ag32_enc"

val bare_asm_conv =
 (computeLib.compset_conv (wordsLib.words_compset())
   [computeLib.Extenders[
     asmLib.add_asm_compset,
     combinLib.add_combin_compset],
    computeLib.Defs [
      UPDATE_def,
      asmSemTheory.write_mem_word_def_compute],
    computeLib.Tys [``:'a asmSem$asm_state``]])

val asm_conv =
  Conv.memoize
    (fn tm =>
      SOME(list_of_triple (dest_asm tm))
      handle HOL_ERR _ => Lib.total (list_of_pair o dest_asm_ok) tm)
    (Redblackmap.mkDict (list_compare Term.compare))
    (fn tm => TypeBase.is_record tm orelse aconv tm T)
    (Feedback.mk_HOL_ERR "ag32Proof" "asm_conv" "")
    bare_asm_conv

fun ag32_enc_conv tm =
  if is_ag32_enc tm
  then ag32_targetLib.ag32_encode_conv tm
  else NO_CONV tm

(*
val bytes_in_memory_tac =
  simp[asmSemTheory.bytes_in_memory_def,EVAL``ag32_startup_addresses``]
  \\ DEP_REWRITE_TAC[init_memory_startup]
  , init_memory_startup |> Q.GEN`n` |> Q.SPEC`0` |> SIMP_RULE(srw_ss())[]]
  \\ simp[LENGTH_hello_startup_code]
  \\ rewrite_tac[hello_startup_code_eq] \\ EVAL_TAC
  \\ fs[word_ls_n2w,word_add_n2w,word_lo_n2w,
        alignmentTheory.byte_aligned_def,
        memory_size_def]
*)

val mem_ok_tac =
  fs[word_ls_n2w,word_add_n2w,word_lo_n2w,
     alignmentTheory.byte_aligned_def,
     word_extract_n2w, memory_size_def,
     GSYM addressTheory.ALIGNED_eq_aligned,
     addressTheory.ALIGNED_n2w,
     bitTheory.BITS_ZERO3 ]

val bounded_bits = Q.prove(`
   ll < 4294967296 ⇒
   ((BIT 0 (ll MOD 256) ⇔ BIT 0 ll) ∧ (BIT 1 (ll MOD 256) ⇔ BIT 1 ll) ∧
   (BIT 2 (ll MOD 256) ⇔ BIT 2 ll) ∧ (BIT 3 (ll MOD 256) ⇔ BIT 3 ll) ∧
   (BIT 4 (ll MOD 256) ⇔ BIT 4 ll) ∧ (BIT 5 (ll MOD 256) ⇔ BIT 5 ll) ∧
   (BIT 6 (ll MOD 256) ⇔ BIT 6 ll) ∧ (BIT 7 (ll MOD 256) ⇔ BIT 7 ll)) ∧
   ((BIT 0 (BITS 31 8 ll MOD 256) ⇔ BIT 8 ll) ∧
   (BIT 1 (BITS 31 8 ll MOD 256) ⇔ BIT 9 ll) ∧
   (BIT 2 (BITS 31 8 ll MOD 256) ⇔ BIT 10 ll) ∧
   (BIT 3 (BITS 31 8 ll MOD 256) ⇔ BIT 11 ll) ∧
   (BIT 4 (BITS 31 8 ll MOD 256) ⇔ BIT 12 ll) ∧
   (BIT 5 (BITS 31 8 ll MOD 256) ⇔ BIT 13 ll) ∧
   (BIT 6 (BITS 31 8 ll MOD 256) ⇔ BIT 14 ll) ∧
   (BIT 7 (BITS 31 8 ll MOD 256) ⇔ BIT 15 ll)) ∧
   ((BIT 0 (BITS 31 8 (BITS 31 8 ll) MOD 256) ⇔ BIT 16 ll) ∧
   (BIT 1 (BITS 31 8 (BITS 31 8 ll) MOD 256) ⇔ BIT 17 ll) ∧
   (BIT 2 (BITS 31 8 (BITS 31 8 ll) MOD 256) ⇔ BIT 18 ll) ∧
   (BIT 3 (BITS 31 8 (BITS 31 8 ll) MOD 256) ⇔ BIT 19 ll) ∧
   (BIT 4 (BITS 31 8 (BITS 31 8 ll) MOD 256) ⇔ BIT 20 ll) ∧
   (BIT 5 (BITS 31 8 (BITS 31 8 ll) MOD 256) ⇔ BIT 21 ll) ∧
   (BIT 6 (BITS 31 8 (BITS 31 8 ll) MOD 256) ⇔ BIT 22 ll) ∧
   (BIT 7 (BITS 31 8 (BITS 31 8 ll) MOD 256) ⇔ BIT 23 ll)) ∧
   ((BIT 0 (BITS 31 8 (BITS 31 8 (BITS 31 8 ll)) MOD 256) ⇔ BIT 24 ll) ∧
   (BIT 1 (BITS 31 8 (BITS 31 8 (BITS 31 8 ll)) MOD 256) ⇔ BIT 25 ll) ∧
   (BIT 2 (BITS 31 8 (BITS 31 8 (BITS 31 8 ll)) MOD 256) ⇔ BIT 26 ll) ∧
   (BIT 3 (BITS 31 8 (BITS 31 8 (BITS 31 8 ll)) MOD 256) ⇔ BIT 27 ll) ∧
   (BIT 4 (BITS 31 8 (BITS 31 8 (BITS 31 8 ll)) MOD 256) ⇔ BIT 28 ll) ∧
   (BIT 5 (BITS 31 8 (BITS 31 8 (BITS 31 8 ll)) MOD 256) ⇔ BIT 29 ll) ∧
   (BIT 6 (BITS 31 8 (BITS 31 8 (BITS 31 8 ll)) MOD 256) ⇔ BIT 30 ll) ∧
   (BIT 7 (BITS 31 8 (BITS 31 8 (BITS 31 8 ll)) MOD 256) ⇔ BIT 31 ll))`,
  strip_tac>>
  CONJ_TAC>- (
    `BITS 7 0 (ll MOD 256) = BITS 7 0 ll` by
      simp[bitTheory.BITS_THM]>>
    fs[GSYM bitTheory.BIT_BITS_THM])>>
  CONJ_TAC>- (
    `BITS 31 8 ll MOD 256 = BITS 15 8 ll` by
      (simp[bitTheory.BITS_THM]>>
      intLib.ARITH_TAC)>>
    simp[bitTheory.BIT_OF_BITS_THM])>>
  CONJ_TAC>- (
    `BITS 31 8 (BITS 31 8 ll) MOD 256 = BITS 23 16 ll` by
      (simp[bitTheory.BITS_THM]>>
      intLib.ARITH_TAC)>>
    simp[bitTheory.BIT_OF_BITS_THM])>>
  `BITS 31 8 (BITS 31 8 (BITS 31 8 ll)) MOD 256 = BITS 31 24 ll` by
    (simp[bitTheory.BITS_THM]>>
    intLib.ARITH_TAC)>>
  simp[bitTheory.BIT_OF_BITS_THM]);

val mem_word_tac =
    rw[word_of_bytes_def,
       set_byte_def, byte_index_def,
       lab_to_targetTheory.ffi_offset_def,
       word_slice_alt_def,heap_size_def,
       EVAL``heap_start_offset``, code_start_offset_def,
       EVAL``ffi_jumps_offset``]>>
    simp[word_add_n2w]>>
    qmatch_goalsub_abbrev_tac` _ = n2w ll`>>
    `ll < dimword(:32)` by
      (fs[Abbr`ll`]>>
      pop_assum mp_tac>>EVAL_TAC>>
      fs[])>>
    pop_assum mp_tac>>simp[]>>
    blastLib.BBLAST_TAC>>
    simp[bounded_bits]

val ag32_const_enc = Q.prove(`
  (∃a b c d.
  ag32_enc (Inst (Const r w)) = [a;b;c;d]) ∨
  ∃a b c d e f g h. ag32_enc (Inst (Const r w)) = [a;b;c;d;e;f;g;h]`,
  rpt (EVAL_TAC>>
  rw[]));

fun LENGTH_ag32_enc_cases_tac
  (g as (asl,w))
  =
  let
    val istrs =
      List.map rand
        (HOLset.listItems
          (HOLset.fromList Term.compare (find_terms is_ag32_enc w)))
  in
    MAP_EVERY (mp_tac o C SPEC (Q.GEN`istr`ag32_enc_lengths)) istrs
    \\ simp[]
    \\ ntac (List.length istrs) strip_tac
    \\ simp[]
  end g

val FLAT_CONS = Q.prove(`
  FLAT (h::t) = h ++ FLAT t`,
  fs[]);

val startup_asm_code_eq =
  startup_asm_code_def |> SPEC_ALL
  |> CONV_RULE(RAND_CONV EVAL)
  |> SIMP_RULE(srw_ss())[]

val startup_code_eq =
  startup_code_def |> SPEC_ALL
  |> REWRITE_RULE[startup_asm_code_eq]
  |> CONV_RULE(RAND_CONV (RAND_CONV ag32_targetLib.ag32_encode_conv))
  |> SIMP_RULE (srw_ss()) [FLAT_compute,FLAT]

(*
val hide_def = Define`
  hide x = x`
*)

Theorem init_asm_state_asm_step:
   ∀code data ffis cl inp.
  SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
  LENGTH inp ≤ stdin_size ∧
  LENGTH ffis ≤ LENGTH FFI_codes ∧
  code_start_offset (LENGTH ffis) + (LENGTH code) + 4 * LENGTH data < memory_size  ∧
  (im =  init_memory code data ffis) ∧
  (asm_state0 =
    ag32_init_asm_state
        (im (cl,inp))
        (ag32_startup_addresses)) ∧
  (mc =
    ag32_machine_config ffis (LENGTH code) (LENGTH data)) ⇒
  let tr =
   (steps (λs i. asm i (s.pc + n2w (LENGTH (ag32_enc i))) s)
     asm_state0
     (startup_asm_code
       (LENGTH ffis)
       (n2w (LENGTH code))
       (n2w (4 * LENGTH data)))) in
  steps_rel (asm_step (ag32_target.config)) asm_state0 tr ∧
  let final_st = LAST (asm_state0::(MAP SND tr)) in
  let num_ffis = LENGTH ffis in
    (final_st.pc = n2w (code_start_offset num_ffis)) ∧
    (read_bytearray final_st.pc (LENGTH code)
      (λa. if a ∈ mc.prog_addresses then
              SOME (final_st.mem a) else NONE ) = SOME code) ∧
    let hs = n2w heap_start_offset in
    let ds = n2w (code_start_offset num_ffis + LENGTH code) in
    (final_st.regs 2 = hs) ∧
    (final_st.regs 4 = hs + n2w heap_size) ∧
    (word_of_bytes F 0w (GENLIST (final_st.mem o ((+) (hs + 0w * 4w)) o n2w) 4) =
     ds) ∧
    (word_of_bytes F 0w (GENLIST (final_st.mem o ((+) (hs + 1w * 4w)) o n2w) 4) =
     ds + n2w (4 * LENGTH data)) ∧
    (word_of_bytes F 0w (GENLIST (final_st.mem o ((+) (hs + 2w * 4w)) o n2w) 4) =
     ds + n2w (4 * LENGTH data)) ∧
    (word_of_bytes F 0w (GENLIST (final_st.mem o ((+) (hs + 3w * 4w)) o n2w) 4) =
     ds) ∧
    (word_of_bytes F 0w (GENLIST (final_st.mem o ((+) (hs + 4w * 4w)) o n2w) 4) =
     ds) ∧
    (∀k. k < 4 * LENGTH data + 4 ⇒
         (final_st.mem (ds + n2w k) =
          (im (cl,inp)) (ds + n2w k)))
Proof
  ntac 6 strip_tac
  \\ qho_match_abbrev_tac`LET (λtr. (_ tr) ∧ P (_ tr)) _`
  \\ rewrite_tac[startup_asm_code_def]
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`steps _ _ (i::tr)`
  \\ simp[steps_def, steps_rel_def]
  \\ qmatch_goalsub_abbrev_tac`asm_step c _ _ s2`
  \\ `c = ag32_config` by simp[Abbr`c`, ag32_targetTheory.ag32_target_def]
  \\ qpat_x_assum`Abbrev (c = _)`kall_tac
  \\ simp[asmSemTheory.asm_step_def, ag32_targetTheory.ag32_config, Abbr`i`]
  \\ qpat_x_assum`Abbrev (s2 = _)`mp_tac
  \\ simp [ag32_machine_configTheory.ag32_init_asm_state_def]
  \\ CONV_TAC (PATH_CONV "lrrr" asm_conv)
  \\ strip_tac
  \\ rewrite_tac[GSYM CONJ_ASSOC]
  \\ conj_tac >- (
    simp[EVAL``heap_start_offset``]>>
    CONV_TAC(ONCE_DEPTH_CONV ag32_enc_conv)>>
    simp[bytes_in_memory_def,EVAL``ag32_startup_addresses``]>>
    DEP_REWRITE_TAC[init_memory_startup]>>
    simp[startup_code_eq])
  \\ conj_tac >- simp[Abbr`s2`]
  \\ conj_tac >- CONV_TAC asm_conv
  \\ qunabbrev_tac`tr`
  (*
  \\ qmatch_goalsub_abbrev_tac`ffi_inst::code_inst::_`
  \\ qmatch_goalsub_abbrev_tac`Inst (Mem _ _ _)::data_inst::Inst (Arith _ )::_`
  \\ `hide
    ((?a b c d e f g h.
    (ag32_enc ffi_inst = [a;b;c;d]) ∨ (ag32_enc ffi_inst = [a;b;c;d;e;f;g;h])) ∧
    hide (?a b c d e f g h.
    (ag32_enc code_inst = [a;b;c;d]) ∨ (ag32_enc code_inst = [a;b;c;d;e;f;g;h])) ∧
    hide (hide (?a b c d e f g h.
    (ag32_enc data_inst = [a;b;c;d]) ∨ (ag32_enc data_inst = [a;b;c;d;e;f;g;h]))))` by
    (unabbrev_all_tac>>simp[hide_def]>>
    metis_tac[ag32_const_enc])
  \\ fs[Abbr`code_inst`,Abbr`ffi_inst`,Abbr`data_inst`]  *)
  \\ rpt (
    qmatch_goalsub_abbrev_tac`steps _ _ (i::tr)`
    \\ simp[steps_def, steps_rel_def, Abbr`s2`]
    \\ qmatch_goalsub_abbrev_tac`asm_step _ _ _ s2`
    \\ simp[asmSemTheory.asm_step_def,
            ag32_targetTheory.ag32_config,
            Abbr`i`]
    \\ qpat_x_assum`Abbrev (s2 = _)`mp_tac
    \\ qpat_abbrev_tac`B = bytes_in_memory _ _ _ _`
    \\ `B`
    by (
      simp[Abbr`B`]
      \\ qmatch_goalsub_abbrev_tac`bytes_in_memory _ (ag32_enc istr)`
      \\ irule bytes_in_memory_get_byte_words
      \\ conj_tac >- ( mp_tac ag32_enc_lengths \\ simp[])
      \\ reverse conj_tac
      >- (
        simp[SUBSET_DEF, IN_all_words, PULL_EXISTS, word_lo_n2w, word_add_n2w,
             ag32_machine_configTheory.ag32_startup_addresses_def,
             EVAL``heap_start_offset``, EVAL``startup_code_size``]
        \\ LENGTH_ag32_enc_cases_tac)
      \\ qexists_tac`F`
      \\ simp[init_memory_def, init_memory_words_def, startup_code_def, startup_asm_code_def]
      \\ rpt (
        rewrite_tac[GSYM APPEND_ASSOC]
        \\ DEP_ONCE_REWRITE_TAC[words_of_bytes_append]
        \\ conj_tac >- simp[bytes_in_word_def, LENGTH_ag32_enc_MOD_4] )
      \\ rewrite_tac[GSYM APPEND_ASSOC]
      \\ qmatch_goalsub_abbrev_tac`words_of_bytes _ (_ istr) ++ lr`
      \\ simp[]
      \\ qmatch_goalsub_abbrev_tac`ll ++ words_of_bytes _ (_ istr)`
      \\ qexists_tac`ll` \\ qexists_tac`lr`
      \\ conj_tac >- (
        simp[IN_all_words, EVAL``code_start_offset _``, word_add_n2w]
        \\ CONV_TAC(ONCE_DEPTH_CONV ag32_enc_conv) \\ simp[]
        \\ gen_tac \\ strip_tac \\ rveq
        \\ rpt (
          IF_CASES_TAC
          >- (
            `F` suffices_by rw[]
            \\ pop_assum mp_tac
            \\ qpat_x_assum`i < _` mp_tac
            \\ LENGTH_ag32_enc_cases_tac ))
        \\ rw[])
      \\ simp[Abbr`ll`, LENGTH_words_of_bytes, bytes_in_word_def, LENGTH_ag32_enc_MOD_4]
      \\ simp[EVAL``heap_start_offset``, EVAL``code_start_offset _``]
      \\ CONV_TAC(ONCE_DEPTH_CONV ag32_enc_conv) \\ simp[]
      \\ LENGTH_ag32_enc_cases_tac )
    \\ CONV_TAC(ONCE_DEPTH_CONV ag32_enc_conv)
    \\ simp[EVAL``heap_start_offset``,EVAL``ag32_startup_addresses``,bytes_in_word_def,Abbr`B`]
    \\ qhdtm_x_assum`bytes_in_memory` kall_tac
    \\ CONV_TAC (PATH_CONV "lrrr" asm_conv)
    \\ strip_tac
    \\ rewrite_tac[GSYM CONJ_ASSOC]
    \\ qmatch_asmsub_abbrev_tac`_ with failed updated_by (K Z)`
    \\ `Z = F` by (
      simp[Abbr`Z`] \\ mem_ok_tac \\
      EVAL_TAC \\ simp[]
      )
    \\ qpat_x_assum`Abbrev(Z = _)` kall_tac
    \\ pop_assum SUBST_ALL_TAC
    \\ conj_tac >- ( simp[Abbr`s2`] \\ mem_ok_tac )
    \\ conj_tac >- CONV_TAC asm_conv
    \\ qunabbrev_tac`tr`)
  \\ simp[steps_def, steps_rel_def]
  \\ simp_tac (std_ss++LET_ss) [Abbr`s2`,Abbr`P`]
  \\ conj_tac >- simp[]
  \\ conj_tac >- (
    simp[lab_to_targetTheory.ffi_offset_def,
         heap_size_def, memory_size_def,
         ag32_targetTheory.ag32_target_def]
    \\ match_mp_tac data_to_word_assignProofTheory.IMP_read_bytearray_GENLIST
    \\ simp[]
    \\ gen_tac \\ strip_tac
    \\ conj_tac >- (
      fs[EVAL``code_start_offset num_ffis``,
         ag32_machine_configTheory.ag32_machine_config_def,
         ag32_machine_configTheory.ag32_prog_addresses_def]>>
      EVAL_TAC>>
      blastLib.BBLAST_TAC>>
      fs[memory_size_def])
    \\ qmatch_goalsub_abbrev_tac`if _ = ll then _ else _`
    \\ `0x501637w <+ ll` by (
      fs[Abbr`ll`,EVAL``code_start_offset num_ffis``,
         ag32_machine_configTheory.ag32_machine_config_def,
         ag32_machine_configTheory.ag32_prog_addresses_def]>>
      EVAL_TAC>>
      blastLib.BBLAST_TAC>>
      fs[memory_size_def])
    \\ rpt (IF_CASES_TAC >-
      (rveq>>fs[WORD_LO]))
    \\ simp[Abbr`ll`]
    \\ metis_tac[init_memory_code])
  \\ conj_tac >- EVAL_TAC
  \\ conj_tac >- (EVAL_TAC \\ simp[])
  \\ conj_tac >- mem_word_tac
  \\ conj_tac >- mem_word_tac
  \\ conj_tac >- mem_word_tac
  \\ conj_tac >- mem_word_tac
  \\ conj_tac >- mem_word_tac
  \\ simp_tac std_ss [asmSemTheory.asm_state_accfupds]
  \\ qpat_x_assum`im = _` SUBST_ALL_TAC
  \\ fs[EVAL``code_start_offset num_ffis``]
  \\ ntac 2 strip_tac
  \\ qmatch_goalsub_abbrev_tac` if _ = ll then _ else _`
  \\ `0x501637w <+ ll` by (
    fs[Abbr`ll`,EVAL``code_start_offset num_ffis``,
       ag32_machine_configTheory.ag32_machine_config_def,
       ag32_machine_configTheory.ag32_prog_addresses_def]>>
    EVAL_TAC>>
    fs[memory_size_def])
  \\ rpt (IF_CASES_TAC >-
    (rveq>>fs[WORD_LO]))
  \\ simp[]
QED

Theorem init_asm_state_RTC_asm_step:
   ∀code data ffis cl inp.
  SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size  ∧
  LENGTH ffis ≤ LENGTH FFI_codes ∧
  code_start_offset (LENGTH ffis) + (LENGTH code) + 4 * LENGTH data < memory_size  ∧
  (im =  init_memory code data ffis) ∧
  (iasmstate =  init_asm_state code data ffis (cl,inp)) ∧
  (asm_state0 =
    ag32_init_asm_state
        (im (cl,inp))
        (ag32_startup_addresses)) ∧
  (mc =
    ag32_machine_config ffis (LENGTH code) (LENGTH data))
  ⇒
   (λx y. ∃i. asm_step ag32_config x i y)^* asm_state0 iasmstate ∧
   let num_ffis = LENGTH ffis in
   let hs = n2w heap_start_offset in
   let ds = n2w (code_start_offset num_ffis + LENGTH code) in
   (iasmstate.pc = n2w (code_start_offset num_ffis)) ∧
   (read_bytearray iasmstate.pc (LENGTH code)
      (λa. if a ∈ mc.prog_addresses then SOME (iasmstate.mem a) else NONE)
      = SOME code) ∧
    (iasmstate.regs 2 = hs) ∧
    (iasmstate.regs 4 = hs + n2w heap_size) ∧
    (word_of_bytes F 0w (GENLIST (iasmstate.mem o ((+)(hs + 0w * 4w)) o n2w) 4)
     = ds) ∧
    (word_of_bytes F 0w (GENLIST (iasmstate.mem o ((+)(hs + 1w * 4w)) o n2w) 4)
     = ds + n2w (4 * LENGTH data)) ∧
    (word_of_bytes F 0w (GENLIST (iasmstate.mem o ((+)(hs + 2w * 4w)) o n2w) 4)
     = ds + n2w (4 * LENGTH data)) ∧
    (word_of_bytes F 0w (GENLIST (iasmstate.mem o ((+)(hs + 3w * 4w)) o n2w) 4)
     = ds) ∧
    (word_of_bytes F 0w (GENLIST (iasmstate.mem o ((+)(hs + 4w * 4w)) o n2w) 4)
     = ds) ∧
    (∀k. k < 4 * LENGTH data + 4 ⇒
      (iasmstate.mem (ds + n2w k) =
       im (cl,inp) (ds + n2w k)))
Proof
  ntac 5 strip_tac>>
  disch_then assume_tac>>
  qspecl_then [`code`,`data`,`ffis`,`cl`,`inp`] mp_tac init_asm_state_asm_step>>
  simp[]>>
  strip_tac>>
  drule steps_rel_LRC>>
  strip_tac>>
  (NRC_LRC |> EQ_IMP_RULE |> #2 |> Q.GEN`n` |> SIMP_RULE bool_ss [PULL_EXISTS] |> drule)
  \\ simp[]
  \\ strip_tac
  \\ drule NRC_RTC
  \\ fs[LAST_MAP_SND_steps_FOLDL, init_asm_state_def]
  \\ fs[ag32_targetTheory.ag32_target_def]
  \\ rfs[]
QED

val _ = export_theory();
