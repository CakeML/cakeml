open preamble
     ffiTheory
     asmTheory asmSemTheory asmPropsTheory
     targetSemTheory;

val _ = new_theory"targetProps";

val _ = set_grammar_ancestry["ffi","asm","targetSem","misc"];

val asserts_restrict = Q.prove(
  `!n next1 next2 s P Q.
      (!k. k <= n ==> (next1 k = next2 k)) ==>
      (asserts n next1 s P Q ==> asserts n next2 s P Q)`,
  Induct \\ full_simp_tac(srw_ss())[asserts_def,LET_DEF]
  \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ REPEAT STRIP_TAC
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ DECIDE_TAC);

val shift_interfer_def = Define `
  shift_interfer k s =
    s with next_interfer := shift_seq k s.next_interfer`

val shift_interfer_intro = Q.prove(
  `shift_interfer k1 (shift_interfer k2 c) =
    shift_interfer (k1+k2) c`,
  full_simp_tac(srw_ss())[shift_interfer_def,shift_seq_def,ADD_ASSOC]);

val evaluate_EQ_evaluate_lemma = Q.prove(
  `!n ms1 c.
      c.target.get_pc ms1 IN c.prog_addresses /\ c.target.state_ok ms1 /\
      interference_ok c.next_interfer (c.target.proj dm) /\
      (!s ms. target_state_rel c.target s ms ==> c.target.state_ok ms) /\
      (!ms1 ms2. (c.target.proj dm ms1 = c.target.proj dm ms2) ==>
                 (c.target.state_ok ms1 = c.target.state_ok ms2)) /\
      (!env.
         interference_ok env (c.target.proj dm) ==>
         asserts n (\k s. env k (c.target.next s)) ms1
           (\ms'. c.target.state_ok ms' /\ c.target.get_pc ms' IN c.prog_addresses)
           (\ms'. target_state_rel c.target s2 ms')) ==>
      ?ms2.
        !k. (evaluate c io (k + (n + 1)) ms1 =
             evaluate (shift_interfer (n+1) c) io k ms2) /\
            target_state_rel c.target s2 ms2`,
  Induct THEN1
   (full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
    \\ full_simp_tac(srw_ss())[asserts_def,LET_DEF]
    \\ SIMP_TAC std_ss [Once evaluate_def] \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `K (c.next_interfer 0)`)
    \\ full_simp_tac(srw_ss())[interference_ok_def] \\ RES_TAC \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ RES_TAC \\ full_simp_tac(srw_ss())[shift_interfer_def,apply_oracle_def]
    \\ METIS_TAC [])
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[arithmeticTheory.ADD_CLAUSES]
  \\ SIMP_TAC std_ss [Once evaluate_def] \\ full_simp_tac(srw_ss())[ADD1] \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ Q.PAT_X_ASSUM `!i. bbb`
       (fn th => ASSUME_TAC th THEN MP_TAC (Q.SPEC
         `\i. c.next_interfer 0` th))
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (full_simp_tac(srw_ss())[interference_ok_def])
  \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC bool_ss [GSYM ADD1,asserts_def] \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ `c.target.state_ok (c.target.next ms1)` by METIS_TAC [interference_ok_def] \\ full_simp_tac(srw_ss())[]
  \\ Q.PAT_X_ASSUM `!ms1 c. bbb ==> ?x. bb`
        (MP_TAC o Q.SPECL [`(c.next_interfer 0 (c.target.next ms1))`,
                    `(c with next_interfer := shift_seq 1 c.next_interfer)`])
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
    THEN1 (full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def])
    THEN1 RES_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC
         `\k. if k = SUC n then c.next_interfer 0 else env k`) \\ full_simp_tac(srw_ss())[]
    \\ MATCH_MP_TAC IMP_IMP
    \\ STRIP_TAC THEN1 (full_simp_tac(srw_ss())[interference_ok_def] \\ srw_tac[][])
    \\ MATCH_MP_TAC asserts_restrict
    \\ srw_tac[][FUN_EQ_THM] \\ `F` by decide_tac)
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[] \\ Q.EXISTS_TAC `ms2` \\ STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `k`)
  \\ full_simp_tac(srw_ss())[GSYM shift_interfer_def,shift_interfer_intro,apply_oracle_def]
  \\ full_simp_tac(srw_ss())[GSYM ADD1]);

val enc_ok_not_empty = Q.prove(
  `enc_ok c /\ asm_ok w c ==> (c.encode w <> [])`,
  METIS_TAC [listTheory.LENGTH_NIL,enc_ok_def]);

val asserts_WEAKEN = Q.prove(
  `!n next s P Q.
      (!x. P x ==> P' x) /\ (!k. k <= n ==> (next k = next' k)) ==>
      asserts n next s P Q ==>
      asserts n next' s P' Q`,
  Induct \\ full_simp_tac(srw_ss())[asserts_def,LET_DEF] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ sg `!k. k <= n ==> (next k = next' k)` \\ RES_TAC
  \\ REPEAT STRIP_TAC \\ FIRST_X_ASSUM MATCH_MP_TAC \\ decide_tac);

val bytes_in_memory_IMP_SUBSET = Q.prove(
  `!xs pc. bytes_in_memory pc xs m d ==> all_pcs (LENGTH xs) pc SUBSET d`,
  Induct \\ full_simp_tac(srw_ss())[all_pcs_def,bytes_in_memory_def]);

val asm_step_IMP_evaluate_step = Q.store_thm("asm_step_IMP_evaluate_step",
  `!c s1 ms1 io i s2.
      encoder_correct c.target /\
      (c.prog_addresses = s1.mem_domain) /\
      interference_ok c.next_interfer (c.target.proj s1.mem_domain) /\
      asm_step c.target.config s1 i s2 /\
      (s2 = asm i (s1.pc + n2w (LENGTH (c.target.config.encode i))) s1) /\
      target_state_rel c.target (s1:'a asm_state) (ms1:'state) ==>
      ?l ms2. !k. (evaluate c io (k + l) ms1 =
                   evaluate (shift_interfer l c) io k ms2) /\
                  target_state_rel c.target s2 ms2 /\ l <> 0`,
  full_simp_tac(srw_ss()) [encoder_correct_def, target_ok_def, LET_DEF]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ full_simp_tac(srw_ss())[]
  \\ Q.EXISTS_TAC `n+1` \\ full_simp_tac(srw_ss())[]
  \\ MATCH_MP_TAC (GEN_ALL evaluate_EQ_evaluate_lemma)
  \\ full_simp_tac(srw_ss())[]
  \\ Q.EXISTS_TAC `s1.mem_domain`
  \\ full_simp_tac(srw_ss())[]
  \\ REPEAT STRIP_TAC
  \\ TRY (RES_TAC \\ fs [target_state_rel_def] \\ NO_TAC)
  >- (full_simp_tac(srw_ss())[asm_step_def, target_state_rel_def]
      \\ IMP_RES_TAC enc_ok_not_empty
      \\ Cases_on `c.target.config.encode i`
      \\ full_simp_tac(srw_ss())[bytes_in_memory_def])
  \\ FIRST_X_ASSUM (K ALL_TAC o Q.SPECL [`\k. env (n - k)`])
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`\k. env (n - k)`])
  \\ MATCH_MP_TAC IMP_IMP
  \\ STRIP_TAC THEN1 full_simp_tac(srw_ss())[interference_ok_def]
  \\ MATCH_MP_TAC asserts_WEAKEN
  \\ SRW_TAC [] []
  >- (POP_ASSUM MP_TAC
      \\ MATCH_MP_TAC SUBSET_IMP
      \\ full_simp_tac(srw_ss())[asm_step_def]
      \\ IMP_RES_TAC bytes_in_memory_IMP_SUBSET)
  \\ full_simp_tac(srw_ss())[FUN_EQ_THM]
  \\ REPEAT STRIP_TAC
  \\ `n - (n - k) = k` by decide_tac
  \\ full_simp_tac(srw_ss())[])
  |> SIMP_RULE std_ss [GSYM PULL_FORALL];

(* basic properties *)

val evaluate_add_clock = Q.store_thm("evaluate_add_clock",
  `∀mc_conf ffi k ms k1 r ms1 st1.
    evaluate mc_conf ffi k ms = (r,ms1,st1) /\ r <> TimeOut ==>
    evaluate mc_conf ffi (k + k1) ms = (r,ms1,st1)`,
  ho_match_mp_tac evaluate_ind >> srw_tac[][] >>
  qhdtm_x_assum`evaluate` mp_tac >>
  simp[Once evaluate_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  simp[Once evaluate_def,SimpR``$==>``] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[apply_oracle_def] >- (
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
    first_x_assum(qspec_then`k1`mp_tac) >> simp[] ) >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  IF_CASES_TAC >> fs[] \\
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  (fn g => subterm split_uncurry_arg_tac (#2 g) g) >> full_simp_tac(srw_ss())[] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  first_x_assum(qspec_then`k1`mp_tac) >> simp[]);

val evaluate_io_events_mono = Q.store_thm("evaluate_io_events_mono",
  `∀mc_conf ffi k ms.
     ffi.io_events ≼ (SND(SND(evaluate mc_conf ffi k ms))).io_events`,
  ho_match_mp_tac evaluate_ind >>
  rpt gen_tac >> strip_tac >>
  simp[Once evaluate_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[apply_oracle_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  TRY BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  TRY BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  TRY BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[call_FFI_def] >> every_case_tac >>
  full_simp_tac(srw_ss())[] >>
  rpt var_eq_tac >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[IS_PREFIX_APPEND]);

val evaluate_add_clock_io_events_mono = Q.store_thm("evaluate_add_clock_io_events_mono",
  `∀mc_conf ffi k ms k'.
   k ≤ k' ⇒
   (SND(SND(evaluate mc_conf ffi k ms))).io_events ≼
   (SND(SND(evaluate mc_conf ffi k' ms))).io_events`,
  ho_match_mp_tac evaluate_ind >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  simp_tac(srw_ss())[Once evaluate_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[]
  >- METIS_TAC[evaluate_io_events_mono] >>
  BasicProvers.TOP_CASE_TAC >> fs [] >>
  TRY BasicProvers.TOP_CASE_TAC >> fs [] >>
  TRY BasicProvers.TOP_CASE_TAC >> fs [] >>
  full_simp_tac(srw_ss())[apply_oracle_def] >>
  TRY BasicProvers.TOP_CASE_TAC >> fs [] >>
  TRY BasicProvers.TOP_CASE_TAC >> fs [] >>
  TRY BasicProvers.TOP_CASE_TAC >> fs [] >>
  TRY BasicProvers.TOP_CASE_TAC >> fs []
  \\ `k ≤ k' + 1` by decide_tac
  \\ res_tac
  \\ CONV_TAC (RAND_CONV (SIMP_CONV std_ss [Once evaluate_def]))
  \\ fs [apply_oracle_def]
  \\ METIS_TAC[evaluate_io_events_mono]);

val _ = export_theory();
