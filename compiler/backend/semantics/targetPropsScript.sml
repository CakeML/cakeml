(*
  Properties about the target semantics
*)
open preamble
     ffiTheory
     asmTheory asmSemTheory asmPropsTheory
     targetSemTheory;

val _ = new_theory"targetProps";

val _ = set_grammar_ancestry["ffi","asm","targetSem","misc"];

Definition shift_interfer_def:
  shift_interfer k s =
    s with next_interfer := shift_seq k s.next_interfer
End

val shift_interfer_intro = Q.prove(
  `shift_interfer k1 (shift_interfer k2 c) =
    shift_interfer (k1+k2) c`,
  full_simp_tac(srw_ss())[shift_interfer_def,shift_seq_def,ADD_ASSOC]);

Theorem bytes_in_memory_SUBSET:
  !p.
  dm SUBSET dm2 /\ bytes_in_memory p xs m dm ==>
  bytes_in_memory p xs m dm2
Proof
  Induct_on `xs` >>
  fs[bytes_in_memory_def] >>
  rpt strip_tac >>
  fs[SUBSET_DEF]
QED

Theorem bytes_in_memory_DIFF:
!p.
    (dm = dm2 DIFF pcs /\ bytes_in_memory p xs m dm2 /\
    DISJOINT pcs {p + n2w i | i | i < LENGTH xs}) ==>
    bytes_in_memory p xs m dm
Proof
  Induct_on `xs` >>
  gvs[bytes_in_memory_def,DISJOINT_DEF,INTER_DEF,EMPTY_DEF,EXTENSION,DIFF_DEF] >>
  rpt strip_tac
  >- (
    first_x_assum $ drule >>
    rw[] >>
    qexists `p + 1w` >>
    rw[] >>
    fs[]
    >- (
       first_x_assum $ qspec_then `x` assume_tac >>
       rw[addressTheory.word_arith_lemma1] >>
       fs[] >>
       `!i. x = p + (n2w (i + 1:num)) ==> ~(i < LENGTH xs)` by (
          rpt strip_tac >>
          first_x_assum $ qspec_then `i+1` drule >>
          disch_then assume_tac >>
          imp_res_tac LESS_MONO_ADD >>
          first_x_assum $ qspec_then `1` assume_tac >>
          fs[]) >>
       fs[]
    )
    >- (
      first_x_assum $ qspec_then `p` assume_tac >>
      rw[] >>
      first_x_assum $ qspec_then `0` assume_tac >>
      fs[]
    )
  )
  >- (
    last_x_assum $ qspec_then `p + 1w` irule >>
    rw[] >>
    first_x_assum $ qspec_then `x` assume_tac >>
    fs[] >>
    rw[addressTheory.word_arith_lemma1] >>
    fs[] >>
    `!i. x = p + (n2w (i + 1:num)) ==> ~(i < LENGTH xs)` by (
      rpt strip_tac >>
      first_x_assum $ qspec_then `i+1` drule >>
      disch_then assume_tac >>
      imp_res_tac LESS_MONO_ADD >>
      first_x_assum $ qspec_then `1` assume_tac >>
      fs[]) >>
    fs[]
  )
QED

Definition ffi_entry_pcs_disjoint_def:
  ffi_entry_pcs_disjoint mc s1 len =
    DISJOINT (set mc.ffi_entry_pcs) {s1.pc + n2w a | a < len}
End

Theorem evaluate_EQ_evaluate_lemma:
  !n ms1 c.
      c.target.get_pc ms1 IN (c.prog_addresses DIFF (set c.ffi_entry_pcs)) /\
      c.target.state_ok ms1 /\
      (c.prog_addresses = dm) ∧
      interference_ok c.next_interfer (c.target.proj dm) /\
      (!s ms. target_state_rel c.target s ms ==> c.target.state_ok ms) /\
      (!ms1 ms2. (c.target.proj dm ms1 = c.target.proj dm ms2) ==>
           (c.target.state_ok ms1 = c.target.state_ok ms2) /\
           (c.target.get_pc ms1 = c.target.get_pc ms2) /\
           (∀a. a ∈ dm ⇒ c.target.get_byte ms1 a = c.target.get_byte ms2 a)) /\
      (!env.
         interference_ok env (c.target.proj dm) ==>
         asserts n (\k s. env k (c.target.next s)) ms1
           (\ms'. c.target.state_ok ms' /\
                  (∀pc. pc ∈ all_pcs (LENGTH (c.target.config.encode i)) init_pc 0 ⇒
                   c.target.get_byte ms' pc = c.target.get_byte ms1 pc) /\
                  c.target.get_pc ms' ∈
                    all_pcs (LENGTH (c.target.config.encode i)) init_pc c.target.config.code_alignment)
           (\ms'. target_state_rel c.target s2 ms')) /\
      (asserts2 (n + 1) (λk. c.next_interfer (n + 1 - k)) c.target.next ms1
        (λms1 ms2. ∀x. x ∉ dm ⇒ c.target.get_byte ms1 x = c.target.get_byte ms2 x)) ∧
      (∃k.
        c.target.get_pc ms1 = init_pc + n2w (k * (2 ** c.target.config.code_alignment)) /\
        k * (2 ** c.target.config.code_alignment) < LENGTH (c.target.config.encode i) /\
        bytes_in_memory init_pc (c.target.config.encode i)
          (c.target.get_byte ms1) (c.prog_addresses DIFF set c.ffi_entry_pcs)) ==>
      ?ms2.
        !k. (evaluate c io (k + (n + 1)) ms1 =
             evaluate (shift_interfer (n+1) c) io k ms2) /\
            target_state_rel c.target s2 ms2
Proof
  Induct THEN1
   (full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
    \\ full_simp_tac(srw_ss())[asserts_def,LET_DEF]
    \\ SIMP_TAC std_ss [Once evaluate_def] \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `K (c.next_interfer 0)`)
    \\ full_simp_tac(srw_ss())[interference_ok_def] \\ RES_TAC \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ RES_TAC \\ full_simp_tac(srw_ss())[shift_interfer_def,apply_oracle_def]
    \\ reverse TOP_CASE_TAC
    >- (
      `F` suffices_by fs[]
      \\ pop_assum mp_tac
      \\ fs[encoded_bytes_in_mem_def]
      \\ asm_exists_tac
      \\ qmatch_goalsub_abbrev_tac`DROP m ls`
      \\ qmatch_goalsub_abbrev_tac`bytes_in_memory _ _ mm dm`
      \\ Q.ISPECL_THEN[`TAKE m ls`,`DROP m ls`,`init_pc`,`mm`,`dm`]mp_tac bytes_in_memory_APPEND
      \\ rfs[]
      \\ metis_tac[DIFF_SUBSET,bytes_in_memory_SUBSET])
    \\ reverse TOP_CASE_TAC
    >- (
      `F` suffices_by fs[]
      \\ pop_assum mp_tac
      \\ fs[Once asserts2_def]
      \\ METIS_TAC[] )
    \\ METIS_TAC [])
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[arithmeticTheory.ADD_CLAUSES]
  \\ SIMP_TAC std_ss [Once evaluate_def] \\ full_simp_tac(srw_ss())[ADD1] \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ Q.PAT_ASSUM `!i. bbb`(qspec_then`λi. c.next_interfer 0`mp_tac)
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (full_simp_tac(srw_ss())[interference_ok_def])
  \\ full_simp_tac(srw_ss())[]
  \\ SIMP_TAC bool_ss [GSYM ADD1,asserts_def] \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ strip_tac
  \\ `c.target.state_ok (c.target.next ms1)` by METIS_TAC [interference_ok_def]
  \\ full_simp_tac(srw_ss())[]
  \\ Q.PAT_X_ASSUM `!ms1 c. bbb ==> ?x. bb`
        (MP_TAC o Q.SPECL [`(c.next_interfer 0 (c.target.next ms1))`,
                    `(c with next_interfer := shift_seq 1 c.next_interfer)`])
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (full_simp_tac(srw_ss())[]
    \\ conj_tac >- (
      fs[all_pcs_thm,SUBSET_DEF,PULL_EXISTS]
      \\ first_assum(mp_then Any mp_tac (GEN_ALL bytes_in_memory_all_pcs))
      \\ fs[SUBSET_DEF]
      \\ disch_then match_mp_tac
      \\ simp[all_pcs_thm]
      \\ METIS_TAC[])
    \\ conj_tac THEN1 (full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def])
    \\ conj_tac THEN1 (rpt strip_tac \\ RES_TAC)
    \\ conj_tac >- (
      rpt strip_tac
      \\ FIRST_ASSUM (MP_TAC o Q.SPEC
           `\k. if k = SUC n then c.next_interfer 0 else env k`) \\ full_simp_tac(srw_ss())[]
      \\ MATCH_MP_TAC IMP_IMP
      \\ STRIP_TAC THEN1 (full_simp_tac(srw_ss())[interference_ok_def] \\ srw_tac[][])
      \\ simp[GSYM ADD1, asserts_def]
      \\ MATCH_MP_TAC asserts_WEAKEN
      \\ simp_tac(srw_ss())[FUN_EQ_THM]
      \\ rw[])
    \\ conj_tac >-  (
      qhdtm_x_assum`asserts2`mp_tac
      \\ simp[Once asserts2_def, shift_seq_def]
      \\ rw[]
      \\ irule asserts2_change_interfer
      \\ simp[]
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ simp[] )
    \\ `c.target.proj dm (c.next_interfer 0 (c.target.next ms1)) =
        c.target.proj dm (c.target.next ms1)` by fs[interference_ok_def]
    \\ qpat_x_assum`∀ms1 ms2. _ ⇒ _` drule
    \\ strip_tac \\ fs[]
    \\ rfs[all_pcs_thm]
    \\ qmatch_asmsub_rename_tac`x * _ < _`
    \\ qexists_tac`x` \\ simp[]
    \\ irule bytes_in_memory_change_mem
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ qx_gen_tac`j` \\ strip_tac
    \\ first_x_assum(qspec_then`init_pc + n2w j`mp_tac)
    \\ impl_tac
    >- (
      imp_res_tac bytes_in_memory_all_pcs
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ fs[all_pcs_thm,SUBSET_DEF,PULL_EXISTS] )
    \\ rw[]
    \\ first_x_assum(qspec_then`λi x. x`mp_tac)
    \\ impl_tac >- fs[interference_ok_def]
    \\ strip_tac
    \\ drule asserts_IMP_FOLDR_COUNT_LIST_LESS
    \\ disch_then(qspec_then`0`mp_tac)
    \\ impl_tac >- fs[]
    \\ simp[]
    \\ strip_tac
    \\ first_x_assum (match_mp_tac o GSYM)
    \\ qexists_tac`j`
    \\ simp[] )
  \\ strip_tac \\ fs[]
  \\ qexists_tac`ms2`
  \\ reverse TOP_CASE_TAC
  >- (
    `F` suffices_by fs[]
    \\ pop_assum mp_tac
    \\ simp[encoded_bytes_in_mem_def]
    \\ qexists_tac`i`
    \\ qmatch_assum_abbrev_tac`k * a < LENGTH bs`
    \\ Q.ISPECL_THEN[`TAKE (k * a) bs`,`DROP (k * a) bs`,`init_pc`]mp_tac bytes_in_memory_APPEND
    \\ simp[]
    \\ METIS_TAC[MULT_COMM,bytes_in_memory_SUBSET,DIFF_SUBSET] )
  \\ rw[]
  \\ fs[GSYM shift_interfer_def, shift_interfer_intro,apply_oracle_def]
  \\ fs[GSYM ADD1]
  \\ simp[ADD1]
  \\ TOP_CASE_TAC
  \\ `F` suffices_by fs[]
  \\ pop_assum mp_tac \\ simp[]
  \\ imp_res_tac asserts2_first \\ fs[]
QED

val enc_ok_not_empty = Q.prove(
  `enc_ok c /\ asm_ok w c ==> (c.encode w <> [])`,
  METIS_TAC [listTheory.LENGTH_NIL,enc_ok_def]);

Theorem asm_step_IMP_evaluate_step = Q.prove(`
  !c s1 ms1 io i s2.
      encoder_correct c.target /\
      (c.prog_addresses = s1.mem_domain) /\
      ffi_entry_pcs_disjoint c s1 (LENGTH $ c.target.config.encode i) /\
      interference_ok c.next_interfer (c.target.proj s1.mem_domain) /\
      asm_step c.target.config s1 i s2 /\
      (* NOTE: Don't delete the following line although it is redundant,
      * it is useful to simplify the lemma after SIMP_RULE *)
      (s2 = asm i (s1.pc + n2w (LENGTH (c.target.config.encode i))) s1) /\
      target_state_rel c.target (s1:'a asm_state) (ms1:'state) ==>
      ?l ms2. !k. (evaluate c io (k + l) ms1 =
                   evaluate (shift_interfer l c) io k ms2) /\
                  target_state_rel c.target s2 ms2 /\ l <> 0`,
  fs[encoder_correct_def,target_ok_def,LET_DEF,ffi_entry_pcs_disjoint_def]
  \\ rw[]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ strip_tac
  \\ qexists_tac`n+1` \\ fs[]
  \\ MATCH_MP_TAC (GEN_ALL evaluate_EQ_evaluate_lemma)
  \\ qexists_tac`s1.pc`
  \\ qexists_tac`i`
  \\ Q.EXISTS_TAC `s1.mem_domain`
  \\ fs[]
  \\ conj_tac
  >- (
    fs[asm_step_def]
    \\ fs[target_state_rel_def]
    \\ imp_res_tac bytes_in_memory_all_pcs
    \\ fs[SUBSET_DEF,all_pcs_thm,PULL_EXISTS]
    \\ conj_tac >- (
      first_x_assum(qspec_then`1`mp_tac)
      \\ simp[]
      \\ disch_then(qspec_then`0`mp_tac)
      \\ simp[]
      \\ disch_then irule
      \\ Cases_on`c.target.config.encode i` \\ fs[]
      \\ pop_assum mp_tac \\ simp[]
      \\ match_mp_tac enc_ok_not_empty
      \\ fs[] )
    >- (
      fs[DISJOINT_DEF,INTER_DEF,EXTENSION,EMPTY_DEF]
      \\ qpat_x_assum `!x. ~(MEM x c.ffi_entry_pcs) \/ _` $ qspec_then `s1.pc`
        assume_tac
      \\ fs[]
      \\ first_x_assum $ qspec_then `0` assume_tac
      \\ gvs[]
      \\ drule enc_ok_not_empty
      \\ strip_tac
      \\ first_x_assum $ qspec_then `i` drule
      \\ fs[]
    ))
  \\ conj_tac >- fs[target_state_rel_def]
  \\ conj_tac >- fs[target_state_rel_def]
  \\ conj_tac >- METIS_TAC[]
  \\ conj_tac >- (
    ntac 2 strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`\k. env (n - k)`])
    \\ simp[]
    \\ impl_tac
    >- fs[interference_ok_def]
    \\ disch_then(mp_tac o CONJUNCT1)
    \\ match_mp_tac asserts_WEAKEN
    \\ simp[] )
  \\ conj_tac >- (
    FIRST_X_ASSUM (MP_TAC o Q.SPECL [`c.next_interfer`])
    \\ impl_tac >- fs[interference_ok_def]
    \\ disch_then(MATCH_ACCEPT_TAC o CONJUNCT2) )
  \\ qexists_tac`0`
  \\ conj_tac >- fs[target_state_rel_def]
  \\ conj_tac >- (
    CCONTR_TAC \\ fs[]
    \\ pop_assum mp_tac
    \\ simp[]
    \\ match_mp_tac enc_ok_not_empty
    \\ fs[asm_step_def] )
  \\ fs[asm_step_def]
  \\ irule bytes_in_memory_change_mem
  \\ qexists `s1.mem`
  \\ conj_tac >- (
    fs[target_state_rel_def]
    \\ rw[]
    \\ first_x_assum (irule o GSYM)
    \\ drule (GEN_ALL bytes_in_memory_all_pcs)
    \\ simp[SUBSET_DEF, all_pcs_thm, PULL_EXISTS]
    \\ disch_then(qspec_then`0`mp_tac) \\ simp[]
  )
  >- (
    irule bytes_in_memory_DIFF
    \\ qexistsl [`s1.mem_domain`, `set c.ffi_entry_pcs`]
    \\ gvs[]
  ))
  |> SIMP_RULE std_ss [GSYM PULL_FORALL];

(* basic properties *)

Theorem evaluate_add_clock:
   ∀mc_conf ffi k ms k1 r ms1 st1.
    evaluate mc_conf ffi k ms = (r,ms1,st1) /\ r <> TimeOut ==>
    evaluate mc_conf ffi (k + k1) ms = (r,ms1,st1)
Proof
  ho_match_mp_tac evaluate_ind >> srw_tac[][] >>
  qhdtm_x_assum`evaluate` mp_tac >>
  simp[Once evaluate_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  simp[Once evaluate_def,SimpR``$==>``] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[apply_oracle_def] >- (
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
    first_x_assum(qspec_then`k1`mp_tac) >> simp[] ) >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  IF_CASES_TAC >> fs[] \\
  rpt (TOP_CASE_TAC \\ fs[])
QED

Theorem evaluate_io_events_mono:
   ∀mc_conf ffi k ms.
     ffi.io_events ≼ (SND(SND(evaluate mc_conf ffi k ms))).io_events
Proof
  ho_match_mp_tac evaluate_ind >>
  rpt gen_tac >> strip_tac >>
  simp[Once evaluate_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  qabbrev_tac `pc_cond = (mc_conf.target.get_pc ms ∈ mc_conf.prog_addresses ∧
                          (¬MEM (mc_conf.target.get_pc ms) mc_conf.ffi_entry_pcs))` >>
  IF_CASES_TAC >> fs[apply_oracle_def] >- (
  IF_CASES_TAC >> fs[] >>
  IF_CASES_TAC >> fs[] >>
  IF_CASES_TAC >> fs[] >>
  IF_CASES_TAC >> fs[] >>
  TOP_CASE_TAC >> fs[] >>
  IF_CASES_TAC >> fs[ELIM_UNCURRY] \\
  Cases_on `(mc_conf.mmio_info x)` \\
  PairCases_on `r` \\
  rpt (TOP_CASE_TAC >> fs[])) \\
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[ELIM_UNCURRY]
  >- (unabbrev_all_tac >> fs[]) >>
  rpt (TOP_CASE_TAC >> fs[]) >>
  gvs[call_FFI_def,bool_case_eq] \\
  rpt (FULL_CASE_TAC >> gvs[]) >>
  irule IS_PREFIX_TRANS>>
  first_assum $ irule_at Any>>fs[IS_PREFIX_APPEND]
QED

Theorem evaluate_add_clock_io_events_mono:
   ∀mc_conf ffi k ms k'.
   k ≤ k' ⇒
   (SND(SND(evaluate mc_conf ffi k ms))).io_events ≼
   (SND(SND(evaluate mc_conf ffi k' ms))).io_events
Proof
  ho_match_mp_tac evaluate_ind >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  simp_tac(srw_ss())[Once evaluate_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[]
  >- METIS_TAC[evaluate_io_events_mono] >>
  `k <= k' + 1` by decide_tac >>
  rpt (TOP_CASE_TAC >> fs[apply_oracle_def]) >>
  res_tac >>
  CONV_TAC (RAND_CONV (SIMP_CONV std_ss [Once evaluate_def])) >>
  fs [apply_oracle_def]
  >- (
    TOP_CASE_TAC >> fs[] >>
    METIS_TAC[evaluate_io_events_mono]
  ) >>
  namedCases_on `mc_conf.mmio_info x` ["r0 r1 r2 r3"] >>
  gvs[] >>
  rpt (TOP_CASE_TAC >> fs[])
QED

Theorem machine_sem_total:
   ∃b. machine_sem mc st ms b
Proof
  Cases_on`∃k t. FST (evaluate mc st k ms) = Halt t`
  >- (
    fs[]
    \\ qexists_tac`Terminate t (SND(SND(evaluate mc st k ms))).io_events`
    \\ simp[targetSemTheory.machine_sem_def]
    \\ Cases_on`evaluate mc st k ms`
    \\ qexists_tac`k` \\ fs[]
    \\ Cases_on`r` \\ fs[] )
  \\ Cases_on`∃k. FST (evaluate mc st k ms) = Error`
  >- ( qexists_tac`Fail` \\ simp[targetSemTheory.machine_sem_def] )
  \\ qexists_tac`Diverge (lprefix_lub$build_lprefix_lub (IMAGE (λk. fromList (SND(SND(evaluate mc st k ms))).io_events) UNIV))`
  \\ simp[targetSemTheory.machine_sem_def]
  \\ conj_tac
  >- (
    rw[]
    \\ Cases_on`evaluate mc st k ms`
    \\ fs[GSYM EXISTS_PROD]
    \\ metis_tac[targetSemTheory.machine_result_nchotomy, FST] )
  \\ irule build_lprefix_lub_thm
  \\ simp[IMAGE_COMPOSE, GSYM o_DEF]
  \\ irule prefix_chain_lprefix_chain
  \\ simp[prefix_chain_def, PULL_EXISTS]
  \\ qx_genl_tac[`k1`,`k2`]
  \\ metis_tac[LESS_EQ_CASES,evaluate_add_clock_io_events_mono]
QED

Theorem machine_sem_unique:
  machine_sem mc ffi ms b1 ∧ machine_sem mc ffi ms b2 ⇒ b1 = b2
Proof
  rw[DefnBase.one_line_ify NONE machine_sem_def] >>
  Cases_on `b1` >> gvs[] >> Cases_on `b2` >> gvs[]
  >- imp_res_tac unique_lprefix_lub
  >- (last_x_assum $ qspec_then `k` assume_tac >> gvs[])
  >- (last_x_assum $ qspec_then `k` assume_tac >> gvs[])
  >- (last_x_assum $ qspec_then `k` assume_tac >> gvs[])
  >- (
    Cases_on `k < k'` >> gvs[LESS_OR_EQ, NOT_LESS] >>
    imp_res_tac LESS_ADD >> gvs[] >> imp_res_tac evaluate_add_clock >> gvs[]
    )
  >- (
    qmatch_asmsub_abbrev_tac `FST ev = Error` >> PairCases_on `ev` >> gvs[] >>
    Cases_on `k < k'` >> gvs[LESS_OR_EQ, NOT_LESS] >>
    imp_res_tac LESS_ADD >> gvs[] >> imp_res_tac evaluate_add_clock >> gvs[]
    )
  >- (last_x_assum $ qspec_then `k` assume_tac >> gvs[])
  >- (
    qmatch_asmsub_abbrev_tac `FST ev = Error` >> PairCases_on `ev` >> gvs[] >>
    Cases_on `k < k'` >> gvs[LESS_OR_EQ, NOT_LESS] >>
    imp_res_tac LESS_ADD >> gvs[] >> imp_res_tac evaluate_add_clock >> gvs[]
    )
QED

Theorem read_ffi_bytearray_IMP_SUBSET_prog_addresses:
   (read_ffi_bytearray mc a l ms = SOME bytes) ==>
    all_words (mc.target.get_reg ms a) (LENGTH bytes) SUBSET
      mc.prog_addresses
Proof
  fs [targetSemTheory.read_ffi_bytearray_def]
  \\ qspec_tac (`mc.target.get_reg ms a`,`x`)
  \\ qspec_tac (`(w2n (mc.target.get_reg ms l))`,`n`)
  \\ qspec_tac (`bytes`,`res`)
  \\ Induct_on `n` \\ fs [read_bytearray_def,all_words_def]
  \\ rw [] \\ fs[option_case_eq] \\ rveq \\ fs []
  \\ fs [all_words_def]
QED

Theorem encoder_correct_asm_step_target_state_rel:
   encoder_correct t ∧
   target_state_rel t s1 ms ∧
   asm_step t.config s1 i s2
   ⇒
   ∃n.
   target_state_rel t s2 (FUNPOW t.next n ms) ∧
   (∀j. j < n ⇒
     (∀pc. pc ∈ all_pcs (LENGTH (t.config.encode i)) s1.pc 0 ⇒
             (t.get_byte (FUNPOW t.next j ms) pc = t.get_byte ms pc)) ∧
     (t.get_pc (FUNPOW t.next j ms) ∈
       all_pcs (LENGTH (t.config.encode i)) s1.pc t.config.code_alignment) ∧
     (t.state_ok (FUNPOW t.next j ms))) ∧
   (∀j x. j ≤ n ∧ x ∉ s1.mem_domain ⇒ (t.get_byte (FUNPOW t.next j ms) x = t.get_byte ms x))
Proof
  rw[asmPropsTheory.encoder_correct_def]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ strip_tac
  \\ first_x_assum(qspec_then`K I`mp_tac)
  \\ impl_tac >- ( EVAL_TAC \\ rw[] )
  \\ srw_tac[ETA_ss][]
  \\ imp_res_tac asmPropsTheory.asserts_IMP_FOLDR_COUNT_LIST
  \\ fs[FOLDR_FUNPOW, LENGTH_COUNT_LIST]
  \\ qexists_tac`SUC n`
  \\ simp[FUNPOW]
  \\ simp[GSYM FORALL_AND_THM]
  \\ gen_tac
  \\ Cases_on`j` \\ fs[]
  >- (
    fs[asmSemTheory.asm_step_def, asmPropsTheory.target_state_rel_def]
    \\ `t.config.encode i <> []`
    by ( fs[asmPropsTheory.target_ok_def, asmPropsTheory.enc_ok_def] )
    \\ Cases_on`t.config.encode i` \\ fs[bytes_in_memory_def]
    \\ fs[asmPropsTheory.all_pcs_thm]
    \\ qexists_tac`0` \\ fs[])
  \\ conj_tac
  >- (
    strip_tac
    \\ drule asmPropsTheory.asserts_IMP_FOLDR_COUNT_LIST_LESS
    \\ disch_then drule
    \\ simp[FOLDR_FUNPOW] )
  \\ ntac 2 strip_tac
  \\ drule asmPropsTheory.asserts2_every
  \\ strip_tac
  \\ qmatch_goalsub_rename_tac`SUC m`
  \\ qho_match_abbrev_tac`P ms (FUNPOW t.next (SUC m) ms)`
  \\ irule FUNPOW_refl_trans_chain
  \\ fs[ADD1,Abbr`P`]
  \\ simp[reflexive_def,transitive_def]
QED

Theorem encoder_correct_RTC_asm_step_target_state_rel:
   encoder_correct t ∧
   target_state_rel t s1 ms ∧
   RTC (λs1 s2. ∃i. asm_step t.config s1 i s2) s1 s2
   ⇒
   ∃n. target_state_rel t s2 (FUNPOW t.next n ms)
Proof
  strip_tac
  \\ first_assum(mp_then (Pat`RTC`) mp_tac (GEN_ALL RTC_lifts_invariants))
  \\ disch_then ho_match_mp_tac
  \\ reverse conj_tac
  >- ( qexists_tac`0` \\ rw[] )
  \\ rw[]
  \\ drule (GEN_ALL encoder_correct_asm_step_target_state_rel)
  \\ disch_then drule
  \\ disch_then drule
  \\ rw[GSYM FUNPOW_ADD]
  \\ asm_exists_tac \\ rw[]
QED

val _ = export_theory();
