open preamble
     stack_allocTheory
     stackSemTheory
     stackPropsTheory

val _ = new_theory"stack_allocProof";


val good_syntax_def = Define `
  (good_syntax (Alloc v) <=> (v = 1)) /\
  (good_syntax ((Seq p1 p2):'a stackLang$prog) <=>
     good_syntax p1 /\ good_syntax p2) /\
  (good_syntax ((If c r ri p1 p2):'a stackLang$prog) <=>
     good_syntax p1 /\ good_syntax p2) /\
  (good_syntax (Call x1 _ x2) <=>
     (case x1 of | SOME (y,r,_,_) => good_syntax y | NONE => T) /\
     (case x2 of SOME (y,_,_) => good_syntax y | NONE => T)) /\
  (good_syntax _ <=> T)`

val get_var_imm_case = prove(
  ``get_var_imm ri s =
    case ri of
    | Reg n => get_var n s
    | Imm w => SOME (Word w)``,
  Cases_on `ri` \\ fs [get_var_imm_def]);

val prog_comp_lemma = prove(
  ``prog_comp = \(n,p). (n,FST (comp n (next_lab p) p))``,
  fs [FUN_EQ_THM,FORALL_PROD,prog_comp_def]);

val lookup_IMP_lookup_compile = prove(
  ``lookup dest s.code = SOME x /\ 30 <= dest ==>
    ?m1 n1. lookup dest (fromAList (compile c (toAList s.code))) =
            SOME (FST (comp m1 n1 x))``,
  fs [lookup_fromAList,compile_def] \\ rw [ALOOKUP_APPEND]
  \\ `ALOOKUP (stubs c) dest = NONE` by
    (fs [stubs_def] \\ rw [] \\ fs [] \\ decide_tac) \\ fs []
  \\ fs [prog_comp_lemma] \\ fs [ALOOKUP_MAP_gen,ALOOKUP_toAList]
  \\ metis_tac []);

val alloc_correct = prove(
  ``alloc w s = (r,t) /\ r <> SOME Error /\
    FLOOKUP s.regs 1 = SOME (Word w) ==>
    ?ck. evaluate
          (Call (SOME (Skip,0,n',m)) (INL 10) NONE,
           s with
           <|use_alloc := F; clock := s.clock + ck;
             code := fromAList (compile c (toAList s.code))|>) =
         (r,
          t with
           <|use_alloc := F; code := fromAList (compile c (toAList s.code))|>)``,
  cheat (* correctness of stubs *));

val find_code_IMP_lookup = prove(
  ``find_code dest regs (s:'a num_map) = SOME x ==>
    ?k. lookup k s = SOME x /\
        (find_code dest regs = ((lookup k):'a num_map -> 'a option))``,
  Cases_on `dest` \\ fs [find_code_def,FUN_EQ_THM]
  \\ every_case_tac \\ fs [] \\ metis_tac []);

val comp_correct = prove(
  ``!p s r t m n c.
      evaluate (p,s) = (r,t) /\ r <> SOME Error /\ good_syntax p /\
      (!k prog. lookup k s.code = SOME prog ==> 30 <= k /\ good_syntax prog) ==>
      ?ck.
        evaluate (FST (comp n m p),
           s with <| clock := s.clock + ck;
                     code := fromAList (stack_alloc$compile c (toAList s.code));
                     use_alloc := F |>) =
          (r, t with
              <| code := fromAList (stack_alloc$compile c (toAList s.code));
                 use_alloc := F |>)``,
  recInduct evaluate_ind \\ rpt strip_tac
  THEN1 (* Skip *)
   (fs [Once comp_def,evaluate_def] \\ rw [] \\ fs [state_component_equality])
  THEN1 (* Halt *)
   (fs [Once comp_def,evaluate_def,get_var_def]
    \\ CASE_TAC \\ fs [] \\ rw [] \\ fs [state_component_equality])
  THEN1 (* Alloc *)
   (fs [evaluate_def,get_var_def]
    \\ fs [Once comp_def,get_var_def]
    \\ every_case_tac \\ fs [good_syntax_def] \\ rw []
    \\ drule alloc_correct \\ fs [])
  THEN1 (* Inst *)
   (fs [Once comp_def] \\ fs [evaluate_def,inst_def]
    \\ CASE_TAC \\ fs [] \\ rw []
    \\ fs [assign_def,word_exp_def,set_var_def,mem_load_def,
         get_var_def,mem_store_def]
    \\ rw [] \\ fs [] \\ fs [state_component_equality]
    \\ every_case_tac \\ fs [markerTheory.Abbrev_def,LET_DEF,word_exp_def]
    \\ fs [state_component_equality] \\ rw [])
  THEN1 (* Get *)
   (fs [Once comp_def,evaluate_def,get_var_def]
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [set_var_def]
    \\ fs [state_component_equality])
  THEN1 (* Set *)
   (fs [Once comp_def,evaluate_def,get_var_def,set_store_def]
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [set_var_def]
    \\ fs [state_component_equality])
  THEN1 (* Tick *)
   (qexists_tac `0` \\ fs [Once comp_def,evaluate_def,dec_clock_def]
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [set_var_def]
    \\ fs [state_component_equality,empty_env_def])
  THEN1 (* Seq *)
   (simp [Once comp_def,dec_clock_def] \\ fs [evaluate_def]
    \\ split_pair_tac \\ fs [LET_DEF]
    \\ split_pair_tac \\ fs [LET_DEF]
    \\ split_pair_tac \\ fs [LET_DEF]
    \\ fs [good_syntax_def,evaluate_def]
    \\ first_x_assum (qspecl_then[`m`,`n`,`c`]mp_tac)
    \\ match_mp_tac IMP_IMP \\ conj_tac
    THEN1 (CCONTR_TAC \\ fs [] \\ fs [] \\ res_tac)
    \\ strip_tac \\ rfs[]
    \\ reverse (Cases_on `res`) \\ fs []
    THEN1 (qexists_tac `ck` \\ fs [AC ADD_COMM ADD_ASSOC,LET_DEF] \\ rw [])
    \\ first_x_assum (qspecl_then[`m'`,`n`,`c`]mp_tac)
    \\ match_mp_tac IMP_IMP \\ conj_tac
    THEN1 (rw [] \\ imp_res_tac evaluate_consts \\ fs [] \\ res_tac \\ fs [])
    \\ strip_tac \\ pop_assum mp_tac
    \\ drule (GEN_ALL evaluate_add_clock) \\ simp []
    \\ disch_then (qspec_then `ck'`assume_tac) \\ strip_tac
    \\ qexists_tac `ck + ck'` \\ fs [AC ADD_COMM ADD_ASSOC]
    \\ imp_res_tac evaluate_consts \\ fs [])
  THEN1 (* Return *)
   (qexists_tac `0` \\ fs [Once comp_def,evaluate_def,get_var_def]
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [get_var_def]
    \\ fs [state_component_equality,empty_env_def])
  THEN1 (* Raise *)
   (qexists_tac `0` \\ fs [Once comp_def,evaluate_def,get_var_def]
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [get_var_def]
    \\ fs [state_component_equality,empty_env_def])
  THEN1 (* If *)
   (simp [Once comp_def] \\ fs [evaluate_def,get_var_def]
    \\ split_pair_tac \\ fs [] \\ split_pair_tac \\ fs []
    \\ every_case_tac \\ fs []
    \\ fs [evaluate_def,get_var_def,get_var_imm_case,good_syntax_def]
    \\ rfs []
    THENL [first_x_assum (qspecl_then[`m`,`n`,`c`]mp_tac),
           first_x_assum (qspecl_then[`m'`,`n`,`c`]mp_tac)]
    \\ match_mp_tac IMP_IMP \\ conj_tac
    \\ TRY (rw [] \\ res_tac \\ fs [] \\ NO_TAC)
    \\ strip_tac \\ fs [] \\ rfs []
    \\ qexists_tac `ck` \\ fs [AC ADD_COMM ADD_ASSOC])
  THEN1 (* JumpLess *)
   (fs [evaluate_def,get_var_def] \\ simp [Once comp_def]
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [good_syntax_def]
    \\ fs [evaluate_def,get_var_def] \\ fs [find_code_def]
    \\ fs [state_component_equality,empty_env_def] \\ res_tac
    \\ imp_res_tac lookup_IMP_lookup_compile
    \\ pop_assum (qspec_then `c` strip_assume_tac) \\ fs []
    THEN1 (qexists_tac `0` \\ fs [state_component_equality,empty_env_def])
    \\ rfs [] \\ fs [PULL_FORALL,dec_clock_def]
    \\ first_x_assum (qspecl_then[`m1`,`n1`,`c`]mp_tac)
    \\ match_mp_tac IMP_IMP \\ conj_tac
    \\ TRY (rw [] \\ res_tac \\ fs [] \\ NO_TAC) \\ strip_tac \\ fs []
    \\ `ck + s.clock - 1 = ck + (s.clock - 1)` by decide_tac
    \\ qexists_tac `ck` \\ fs [AC ADD_COMM ADD_ASSOC])
  THEN1 (* Call *)
   (fs [evaluate_def] \\ Cases_on `ret` \\ fs [] THEN1
     (Cases_on `find_code dest s.regs s.code` \\ fs []
      \\ every_case_tac \\ fs [empty_env_def] \\ rw [] \\ fs []
      \\ fs [good_syntax_def] \\ simp [Once comp_def,evaluate_def]
      \\ drule find_code_IMP_lookup \\ fs [] \\ rw [] \\ fs [] \\ fs []
      \\ res_tac \\ imp_res_tac lookup_IMP_lookup_compile
      \\ pop_assum (strip_assume_tac o SPEC_ALL) \\ fs []
      THEN1 (qexists_tac `0` \\ fs [empty_env_def,state_component_equality])
      THEN1 (qexists_tac `0` \\ fs [empty_env_def,state_component_equality])
      \\ fs [dec_clock_def]
      \\ first_x_assum (qspecl_then[`n1`,`m1`,`c`]mp_tac)
      \\ match_mp_tac IMP_IMP \\ conj_tac
      \\ TRY (rw [] \\ res_tac \\ fs [] \\ NO_TAC) \\ strip_tac \\ fs []
      \\ `ck + s.clock - 1 = ck + (s.clock - 1)` by decide_tac
      \\ qexists_tac `ck` \\ fs [AC ADD_COMM ADD_ASSOC])
    \\ qmatch_assum_rename_tac `good_syntax (Call (SOME z) dest handler)`
    \\ PairCases_on `z` \\ fs [] \\ simp [Once comp_def] \\ fs []
    \\ split_pair_tac \\ fs []
    \\ Cases_on `find_code dest (s.regs \\ z1) s.code` \\ fs []
    \\ drule find_code_IMP_lookup \\ rw [] \\ fs []
    \\ res_tac \\ imp_res_tac lookup_IMP_lookup_compile
    \\ pop_assum (qspec_then`c`strip_assume_tac) \\ fs [good_syntax_def]
    \\ Cases_on `s.clock = 0` \\ fs [] THEN1
     (rw [] \\ fs [] \\ every_case_tac \\ fs []
      \\ TRY split_pair_tac \\ fs [evaluate_def]
      \\ qexists_tac `0` \\ fs []
      \\ fs [empty_env_def,state_component_equality])
    \\ Cases_on `evaluate (x,dec_clock (set_var z1 (Loc z2 z3) s))`
    \\ Cases_on `q` \\ fs []
    \\ Cases_on `x'` \\ fs [] \\ rw [] \\ TRY
     (every_case_tac \\ fs [] \\ TRY split_pair_tac
      \\ fs [evaluate_def,dec_clock_def,set_var_def]
      \\ first_x_assum (qspecl_then[`n1`,`m1`,`c`]mp_tac)
      \\ match_mp_tac IMP_IMP \\ conj_tac
      \\ TRY (rw [] \\ res_tac \\ fs [] \\ NO_TAC) \\ strip_tac \\ fs []
      \\ `ck + s.clock - 1 = s.clock - 1 + ck` by decide_tac
      \\ qexists_tac `ck` \\ fs [] \\ NO_TAC)
    THEN1
     (Cases_on `w = Loc z2 z3` \\ rw [] \\ fs []
      \\ first_x_assum (qspecl_then[`m`,`n`,`c`]mp_tac)
      \\ match_mp_tac IMP_IMP \\ conj_tac
      \\ TRY (imp_res_tac evaluate_consts \\ fs []
              \\ rw [] \\ res_tac \\ fs [] \\ NO_TAC)
      \\ strip_tac \\ fs [] \\ rfs []
      \\ first_x_assum (qspecl_then[`n1`,`m1`,`c`]mp_tac)
      \\ match_mp_tac IMP_IMP \\ conj_tac
      \\ TRY (imp_res_tac evaluate_consts \\ fs []
              \\ rw [] \\ res_tac \\ fs [] \\ NO_TAC) \\ rw []
      \\ Cases_on `handler` \\ fs []
      \\ TRY (PairCases_on `x'` \\ ntac 2 (split_pair_tac \\ fs []))
      \\ fs [evaluate_def,dec_clock_def,set_var_def]
      \\ first_assum (mp_tac o Q.SPEC `ck` o
             MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
             (evaluate_add_clock |> GEN_ALL))) \\ fs []
      \\ rw [] \\ qexists_tac `ck' + ck` \\ fs [AC ADD_COMM ADD_ASSOC]
      \\ `ck + (ck' + (s.clock - 1)) = ck + (ck' + s.clock) - 1` by decide_tac
      \\ fs [] \\ imp_res_tac evaluate_consts \\ fs [])
    \\ Cases_on `handler` \\ fs[]
    \\ fs [evaluate_def,dec_clock_def,set_var_def]
    THEN1
     (first_x_assum (qspecl_then[`n1`,`m1`,`c`]mp_tac)
      \\ match_mp_tac IMP_IMP \\ conj_tac
      \\ TRY (imp_res_tac evaluate_consts \\ fs []
              \\ rw [] \\ res_tac \\ fs [] \\ NO_TAC) \\ rw []
      \\ `ck + s.clock - 1 = s.clock - 1 + ck` by decide_tac
      \\ qexists_tac `ck` \\ fs [])
    \\ PairCases_on `x'` \\ fs []
    \\ split_pair_tac \\ fs []
    \\ fs [evaluate_def,dec_clock_def,set_var_def]
    \\ Cases_on `w = Loc x'1 x'2` \\ rw [] \\ fs []
    \\ ntac 2 (pop_assum mp_tac)
    \\ first_x_assum (qspecl_then[`n1`,`m1`,`c`]mp_tac)
    \\ match_mp_tac IMP_IMP \\ conj_tac
    \\ TRY (imp_res_tac evaluate_consts \\ fs []
            \\ rw [] \\ res_tac \\ fs [] \\ NO_TAC) \\ rw [] \\ rfs[]
    \\ first_x_assum (qspecl_then[`m'`,`n`,`c`]mp_tac)
    \\ match_mp_tac IMP_IMP \\ conj_tac
    \\ TRY (imp_res_tac evaluate_consts \\ fs []
            \\ rw [] \\ res_tac \\ fs [] \\ NO_TAC) \\ rw []
    \\ ntac 2 (pop_assum mp_tac)
    \\ first_assum (mp_tac o Q.SPEC `ck'` o
             MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
             (evaluate_add_clock |> GEN_ALL))) \\ fs [] \\ rw []
    \\ qexists_tac `ck+ck'` \\ fs []
    \\ `ck + ck' + s.clock - 1 = s.clock - 1 + ck + ck'` by decide_tac \\ fs[]
    \\ imp_res_tac evaluate_consts \\ fs [])
  THEN1 (* FFI *)
   (qexists_tac `0` \\ fs [Once comp_def,evaluate_def,get_var_def]
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [get_var_def]
    \\ fs [state_component_equality,empty_env_def,LET_DEF])
  \\ qexists_tac `0` \\ fs [Once comp_def,evaluate_def,get_var_def,set_var_def]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs [get_var_def]
  \\ fs [state_component_equality,empty_env_def,LET_DEF]);

val compile_semantics = Q.store_thm("compile_semantics",
  `(!k prog. lookup k s.code = SOME prog ==> 30 ≤ k /\ good_syntax prog) /\
   semantics start s <> Fail
   ==>
   semantics start (s with <|
                      code := fromAList (stack_alloc$compile c (toAList s.code));
                      use_alloc := F |>) =
   semantics start s`,
  simp[GSYM AND_IMP_INTRO] >> strip_tac >>
  simp[semantics_def] >>
  IF_CASES_TAC >> fs[] >>
  DEEP_INTRO_TAC some_intro >> fs[] >>
  conj_tac >- (
    gen_tac >> ntac 2 strip_tac >>
    IF_CASES_TAC >> fs[] >- (
      first_x_assum(qspec_then`k'`mp_tac)>>simp[]>>
      (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
      simp[] >>
      qmatch_assum_rename_tac`_ = (res,_)` >>
      Cases_on`res=SOME Error`>>simp[]>>
      drule comp_correct >>
      simp[good_syntax_def,RIGHT_FORALL_IMP_THM] >>
      discharge_hyps >- metis_tac[] >>
      simp[comp_def] >>
      disch_then(qspec_then`c`strip_assume_tac) >>
      qpat_assum`_ ≠ SOME TimeOut`mp_tac >>
      (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
      strip_tac >>
      drule (Q.GEN`extra`evaluate_add_clock) >>
      disch_then(qspec_then`ck`mp_tac) >> fs[] >>
      strip_tac >> fsrw_tac[ARITH_ss][] >> rw[]) >>
    DEEP_INTRO_TAC some_intro >> fs[] >>
    conj_tac >- (
      rw[] >>
      Cases_on`r=TimeOut`>>fs[]>-(
        qmatch_assum_abbrev_tac`evaluate (e,ss) = (SOME TimeOut,_)` >>
        qspecl_then[`k'`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
        simp[Abbr`ss`] >>
        (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
        simp[] >> strip_tac >>
        drule comp_correct >>
        simp[RIGHT_FORALL_IMP_THM] >>
        discharge_hyps >- (
          simp[Abbr`e`,good_syntax_def] >>
          reverse conj_tac >- metis_tac[] >>
          rpt(first_x_assum(qspec_then`k+k'`mp_tac))>>rw[] ) >>
        simp[Abbr`e`,comp_def] >>
        disch_then(qspec_then`c`strip_assume_tac) >>
        Cases_on`t'.ffi.final_event`>>fs[] >- (
          ntac 2 (rator_x_assum`evaluate`mp_tac) >>
          drule (GEN_ALL evaluate_add_clock) >>
          disch_then(qspec_then`ck+k`mp_tac) >>
          simp[] >>
          discharge_hyps >- (strip_tac >> fs[]) >>
          simp[] >> ntac 3 strip_tac >>
          rveq >> fs[] >>
          `t'.ffi = r''.ffi` by fs[state_component_equality] >>
          fs[] >>
          Cases_on`t.ffi.final_event`>>fs[] >>
          rfs[] ) >>
        rator_x_assum`evaluate`mp_tac >>
        qmatch_assum_abbrev_tac`evaluate (e,ss) = (_,t')` >>
        qspecl_then[`ck+k`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
        simp[Abbr`ss`] >>
        ntac 2 strip_tac >> fs[] >>
        Cases_on`t.ffi.final_event`>>fs[] >>
        rfs[] ) >>
      rator_x_assum`evaluate`mp_tac >>
      drule (GEN_ALL evaluate_add_clock) >>
      disch_then(qspec_then`k'`mp_tac) >>
      simp[] >> strip_tac >>
      drule comp_correct >>
      simp[RIGHT_FORALL_IMP_THM] >>
      discharge_hyps >- (
        simp[good_syntax_def] >>
        reverse conj_tac >- metis_tac[] >>
        rpt(first_x_assum(qspec_then`k+k'`mp_tac))>>rw[] ) >>
      simp[comp_def] >>
      disch_then(qspec_then`c`strip_assume_tac) >>
      strip_tac >>
      qmatch_assum_abbrev_tac`evaluate (e,ss) = _` >>
      qspecl_then[`ck+k`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
      simp[Abbr`ss`] >> strip_tac >>
      Cases_on`t'.ffi.final_event`>>fs[]>>
      drule (GEN_ALL evaluate_add_clock) >>
      disch_then(qspec_then`ck+k`mp_tac) >>
      simp[] >>
      discharge_hyps >- (strip_tac >> fs[]) >>
      strip_tac >> fs[] >> rveq >> fs[] >>
      `t.ffi = t'.ffi` by fs[state_component_equality] >>
      BasicProvers.FULL_CASE_TAC >> fs[] >> rfs[] ) >>
    drule comp_correct >>
    simp[RIGHT_FORALL_IMP_THM] >>
    discharge_hyps >- (
      simp[good_syntax_def] >>
      reverse conj_tac >- metis_tac[] >>
      rpt(first_x_assum(qspec_then`k`mp_tac))>>rw[]) >>
    simp[comp_def] >>
    disch_then(qspec_then`c`strip_assume_tac) >>
    asm_exists_tac >> simp[] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    BasicProvers.TOP_CASE_TAC >> fs[]) >>
  strip_tac >>
  IF_CASES_TAC >> fs[] >- (
    first_x_assum(qspec_then`k`mp_tac)>>simp[]>>
    first_x_assum(qspec_then`k`mp_tac)>>
    (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
    simp[] >>
    rw[] >> BasicProvers.TOP_CASE_TAC >> fs[] >>
    drule comp_correct >>
    simp[good_syntax_def,comp_def] >>
    qexists_tac`c`>>simp[] >>
    conj_tac >- metis_tac[] >>
    rw[] >>
    qpat_assum`_ ≠ SOME TimeOut`mp_tac >>
    (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >> rw[] >>
    drule (GEN_ALL evaluate_add_clock) >>
    disch_then(qspec_then`ck`mp_tac)>>simp[] ) >>
  DEEP_INTRO_TAC some_intro >> fs[] >>
  conj_tac >- (
    rw[] >>
    qpat_assum`∀k t. _`(qspec_then`k`mp_tac) >>
    (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
    simp[] >>
    last_x_assum mp_tac >>
    last_x_assum(qspec_then`k`mp_tac) >>
    rw[] >> BasicProvers.TOP_CASE_TAC >> fs[] >>
    drule comp_correct >>
    simp[good_syntax_def,comp_def] >>
    qexists_tac`c`>>simp[] >>
    conj_tac >- metis_tac[] >>
    rw[] >>
    Cases_on`r=TimeOut`>>fs[]>-(
      qmatch_assum_abbrev_tac`evaluate (e,ss) = (_,t)` >>
      qspecl_then[`ck`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
      simp[Abbr`ss`] >>
      Cases_on`t.ffi.final_event`>>fs[] >>
      rpt strip_tac >> fs[] ) >>
    rator_x_assum`evaluate`mp_tac >>
    drule (GEN_ALL evaluate_add_clock) >>
    disch_then(qspec_then`ck`mp_tac)>>simp[] ) >>
  rw[] >>
  qmatch_abbrev_tac`build_lprefix_lub l1 = build_lprefix_lub l2` >>
  `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
    suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub] >>
  conj_asm1_tac >- (
    UNABBREV_ALL_TAC >>
    conj_tac >>
    Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
    REWRITE_TAC[IMAGE_COMPOSE] >>
    match_mp_tac prefix_chain_lprefix_chain >>
    simp[prefix_chain_def,PULL_EXISTS] >>
    qx_genl_tac[`k1`,`k2`] >>
    qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
    metis_tac[
      LESS_EQ_EXISTS,
      evaluate_add_clock_io_events_mono
        |> CONV_RULE(SWAP_FORALL_CONV)
        |> Q.SPEC`s with <| use_alloc := F; clock := k; code := c|>`
        |> SIMP_RULE(srw_ss())[],
      evaluate_add_clock_io_events_mono
        |> CONV_RULE(SWAP_FORALL_CONV)
        |> Q.SPEC`s with <| clock := k |>`
        |> SIMP_RULE(srw_ss())[]]) >>
  simp[equiv_lprefix_chain_thm] >>
  unabbrev_all_tac >> simp[PULL_EXISTS] >>
  ntac 2 (pop_assum kall_tac) >>
  simp[LNTH_fromList,PULL_EXISTS] >>
  simp[GSYM FORALL_AND_THM] >>
  rpt gen_tac >>
  (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >> fs[] >>
  (fn g => subterm (fn tm => Cases_on`^(assert (fn tm => has_pair_type tm andalso free_in tm (#2 g)) tm)`) (#2 g) g) >> fs[] >>
  drule comp_correct >>
  simp[comp_def,RIGHT_FORALL_IMP_THM] >>
  discharge_hyps >- (
    simp[good_syntax_def] >>
    reverse conj_tac >- metis_tac[] >>
    rpt(first_x_assum(qspec_then`k`mp_tac))>>rw[] ) >>
  disch_then(qspec_then`c`strip_assume_tac) >>
  reverse conj_tac >- (
    rw[] >>
    qexists_tac`ck+k`>>simp[] ) >>
  rw[] >>
  qexists_tac`k`>>simp[] >>
  ntac 2 (rator_x_assum`evaluate`mp_tac) >>
  qmatch_assum_abbrev_tac`evaluate (e,ss) = _` >>
  qspecl_then[`ck`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
  simp[Abbr`ss`] >>
  ntac 3 strip_tac >> fs[] >>
  fs[IS_PREFIX_APPEND] >>
  simp[EL_APPEND1]);

val make_init_def = Define `
  make_init code s = s with <| code := code; use_alloc := T |>`;

val prog_comp_lambda = Q.store_thm("prog_comp_lambda",
  `prog_comp = λ(n,p). ^(rhs (concl (SPEC_ALL prog_comp_def)))`,
  rw[FUN_EQ_THM,prog_comp_def,LAMBDA_PROD,FORALL_PROD]);

val make_init_semantics = Q.store_thm("make_init_semantics",
  `(!k prog. ALOOKUP code k = SOME prog ==> 30 ≤ k /\ good_syntax prog) /\
   ~s.use_alloc /\ s.code = fromAList (compile c code) /\
   ALL_DISTINCT (MAP FST code) /\
   semantics start (make_init (fromAList code) s) <> Fail ==>
   semantics start s = semantics start (make_init (fromAList code) s)`,
  rw [] \\ drule (ONCE_REWRITE_RULE[CONJ_COMM]compile_semantics)
  \\ fs [make_init_def,lookup_fromAList]
  \\ discharge_hyps THEN1 (rw [] \\ res_tac \\ fs [])
  \\ disch_then (assume_tac o GSYM)
  \\ fs [] \\ AP_TERM_TAC \\ fs [state_component_equality]
  \\ fs [spt_eq_thm,wf_fromAList,lookup_fromAList,compile_def]
  \\ rw []
  \\ rw[ALOOKUP_APPEND] \\ BasicProvers.CASE_TAC
  \\ simp[prog_comp_lambda,ALOOKUP_MAP_gen]
  \\ simp[ALOOKUP_toAList,lookup_fromAList]);

val _ = export_theory();
