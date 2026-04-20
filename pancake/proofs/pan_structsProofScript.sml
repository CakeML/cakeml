(*
  Correctness proof for pan_structs

  Side-stepped for now as the "named_structs_ok" switch in the semantics
  prevents the structures adjusted by the pan_structs phase from appearing
  in a verified program.
*)
Theory pan_structsProof
Ancestors
  panSem pan_structs panProps panLang
Libs
  preamble

Theorem compile_exps_eq_map[local]:
  compile_exps ctxt = MAP (compile_exp ctxt)
Proof
  rw [FUN_EQ_THM]
  \\ Induct_on `x`
  \\ simp [compile_exp_def]
QED

Theorem opt_mmap_eq_some_el:
  !xs ys. (OPT_MMAP f xs = SOME ys) = (LENGTH xs = LENGTH ys /\
    (!n. n < LENGTH ys ==> f (EL n xs) = SOME (EL n ys)))
Proof
  Induct_on `xs`
  \\ csimp []
  \\ rw []
  \\ Cases_on `ys` \\ fs []
  \\ simp [LT_SUC, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS]
  \\ metis_tac []
QED

Theorem compile_shape_eq_pre[local]:
  (!x shape. ss = x /\ is_wf_shape_nil shape ==>
    compile_shape ss shape = shape) ∧
  (!x shapes. ss = x /\ EVERY is_wf_shape_nil shapes ==>
    compile_shapes ss shapes = shapes)
Proof
  ho_match_mp_tac compile_shape_ind
  \\ simp [compile_shape_def, is_wf_shape_def, SF ETA_ss]
QED

Theorem compile_shape_eq = Q.GEN `ss` compile_shape_eq_pre |> SIMP_RULE bool_ss []

Theorem compile_exp_correct_mmap_helper[local]:
  !es vs. OPT_MMAP (\e. eval s e) es = SOME vs /\
  (!e. MEM e es ==> (!v. eval s e = SOME v ==> eval s (compile_exp ctxt e) = SOME v)) ==>
  OPT_MMAP (λa. eval s a) (compile_exps ctxt es) = SOME vs
Proof
  Induct
  \\ simp [compile_exp_def, DISJ_IMP_THM, FORALL_AND_THM]
  \\ rw []
QED

Theorem compile_exp_correct:
  ∀s e v.
  eval s e = SOME v ∧
  s.structs = []
  ⇒
  eval s (compile_exp ctxt e) = SOME v
Proof
  recInduct (name_ind_cases [] eval_ind) >> rpt conj_tac
  >> rpt (gen_tac ORELSE disch_tac)
  >~ [`NStruct`]
  >- (
    fs [eval_def, UNCURRY_EQ] \\ fs []
  )
  >~ [`NField`]
  >- (
    gs [eval_def, UNCURRY_EQ, v_case_eq, option_case_eq]
  )
  >~ [`RField`]
  >- (
    gvs [eval_def, option_case_eq, v_case_eq, compile_exp_def, is_wf_shape_v_def]
    >> fs [FORALL_AND_THM, EVERY_EL]
  )
  >~ [`Load`]
  >- (
    gvs [eval_def, AllCaseEqs (), compile_exp_def, is_wf_shape_v_def]
    >> simp [compile_shape_eq]
  )
  >> gvs [eval_def, compile_exp_def, AllCaseEqs (), is_wf_shape_v_def]
  >> imp_res_tac FEVERY_FLOOKUP
  >> fs []
  >> dxrule compile_exp_correct_mmap_helper
  >> simp []
QED

Theorem compile_exp_correct_eq[local]:
  ∀s e v.
  eval s e <> NONE /\ s.structs = []
  ⇒
  eval s (compile_exp ctxt e) = eval s e
Proof
  rw []
  \\ Cases_on `eval s e` \\ fs []
  \\ dxrule compile_exp_correct
  \\ simp []
QED

Theorem evaluate_structs_code_inv[local]:
  evaluate (p, s) = (res, s') ==>
  s'.structs = s.structs ∧ s'.code = s.code
Proof
  rw [] \\ imp_res_tac evaluate_invariants
QED

Theorem eval_upd_code_eq2[local]:
  eval (t with code := code) = eval t
Proof
  simp [eval_upd_code_eq, FUN_EQ_THM]
QED

Definition code_rel_def:
  code_rel code1 code2 = (
    !nm sh prog. FLOOKUP code1 nm = SOME (sh, prog) ==>
      ?ctxt. FLOOKUP code2 nm = SOME (sh, compile ctxt prog))
End

Theorem code_rel_imp[local] = hd (RES_CANON code_rel_def)

Theorem compile_correct:
  ∀ p s res s' ctxt.
  evaluate (p, s) = (res, s') ∧
  code_rel s.code code ∧
  s.structs = [] ∧
  FEVERY (λ(nm,v). is_wf_shape_v_nil v) s.locals ∧
  FEVERY (λ(nm,v). is_wf_shape_v_nil v) s.globals ∧
  res ≠ SOME Error
  ⇒
  evaluate (compile ctxt p, (s with code := code)) = (res, (s' with code := code))
Proof
  recInduct (name_ind_cases [] evaluate_ind) >> rpt conj_tac
  >> rpt (gen_tac ORELSE disch_tac)
  >> fs [compile_def]
  >~ [`While`]
  >- (
    qpat_x_assum `evaluate _ = _` mp_tac
    >> ONCE_REWRITE_TAC [evaluate_def]
    >> strip_tac
    >> gs [AllCaseEqs (), UNCURRY_EQ, eval_upd_code_eq]
    >> imp_res_tac evaluate_structs_code_inv
    >> imp_res_tac evaluate_is_wf_shape_invariant
    >> gvs [compile_exp_correct_eq, dec_clock_def, empty_locals_def]
  )
  >~ [`Dec`]
  >- (
    gs [evaluate_def, AllCaseEqs (), UNCURRY_EQ, eval_upd_code_eq]
    >> imp_res_tac eval_is_wf_shape_v
    >> imp_res_tac evaluate_structs_code_inv
    >> imp_res_tac evaluate_is_wf_shape_invariant
    >> gvs [FEVERY_FUPDATE, fevery_to_drestrict]
    >> simp [compile_exp_correct_eq, compile_shape_eq, is_wf_shape_v_nil]
  )
  >~ [`Call`]
  >- (
    every_case_tac
    >> gvs [evaluate_def, option_case_eq, pair_case_eq, eval_upd_code_eq2]
    >> drule_then (drule_then assume_tac) lookup_code_wf_shape_invariant_step
    >> gs []
    >> gvs [evaluate_def, lookup_code_def, AllCaseEqs (), UNCURRY_EQ,
            compile_exp_correct_eq, eval_upd_code_eq2]
    >> imp_res_tac code_rel_imp
    >> drule_then (irule_at Any) (SIMP_RULE bool_ss [SF ETA_ss] compile_exp_correct_mmap_helper)
    >> simp [compile_exp_correct_eq, FLOOKUP_FMAP_MAP2, empty_locals_def]
    >> imp_res_tac evaluate_structs_code_inv
    >> imp_res_tac evaluate_is_wf_shape_invariant
    >> gs [dec_clock_def, set_var_def, set_kvar_def, set_global_def, FEVERY_FUPDATE, fevery_to_drestrict]
    >> every_case_tac >> simp []
  )
  >~ [`DecCall`]
  >- (
    gvs [evaluate_def, option_case_eq, pair_case_eq, eval_upd_code_eq2]
    >> drule_then (drule_then assume_tac) lookup_code_wf_shape_invariant_step
    >> gs []
    >> gvs [evaluate_def, lookup_code_def, AllCaseEqs (), UNCURRY_EQ, compile_exp_correct_eq]
    >> imp_res_tac code_rel_imp
    >> drule_then (irule_at Any) (SIMP_RULE bool_ss [SF ETA_ss] compile_exp_correct_mmap_helper)
    >> simp [compile_exp_correct_eq, FLOOKUP_FMAP_MAP2, empty_locals_def]
    >> imp_res_tac evaluate_structs_code_inv
    >> imp_res_tac evaluate_is_wf_shape_invariant
    >> gs [dec_clock_def, set_var_def, FEVERY_FUPDATE, fevery_to_drestrict,
        compile_shape_eq, is_wf_shape_v_nil]
  )
  >> gs [evaluate_def, AllCaseEqs (), UNCURRY_EQ, compile_exp_correct_eq,
        eval_upd_code_eq2, sh_mem_load_def, sh_mem_store_def]
  >> simp [GSYM (Q.ISPEC `compile ctxt` boolTheory.COND_RAND)]
  >> imp_res_tac evaluate_structs_code_inv
  >> imp_res_tac evaluate_is_wf_shape_invariant
  >> fs [set_kvar_def, set_var_def, set_global_def] >> every_case_tac
  >> gvs [empty_locals_def, dec_clock_def]
QED

Theorem compile_decs_correct:
  !s decs ctxt code. evaluate_decls s decs = SOME s' ∧
  code_rel s.code code ∧
  ctxt.structs = [] ∧ s.structs = [] ∧ s.locals = FEMPTY ∧
  FEVERY (λ(nm,v). is_wf_shape_v_nil v) s.globals ==>
  ?code'.
  evaluate_decls (s with code := code) (FST (compile_decs ctxt decs)) =
    SOME (s' with code := code') ∧
  code_rel s'.code code'
Proof
  recInduct (name_ind_cases [] evaluate_decls_ind)
  >> rw []
  >> fs [compile_decs_def, evaluate_decls_def]
  >- (
    metis_tac []
  )
  >- (
    gs [option_case_eq, bool_case_eq]
    >> simp [UNCURRY]
    >> fs [evaluate_decls_def, compile_exp_correct_eq,
        eval_upd_code_eq |> Q.SPEC `st with locals := l` |> SIMP_RULE (srw_ss ()) []]
    >> imp_res_tac eval_is_wf_shape_v
    >> gs [FEVERY_FEMPTY, compile_shape_eq, is_wf_shape_v_nil]
    >> fs [FEVERY_FUPDATE, fevery_to_drestrict]
  )
  >- (
    simp [UNCURRY]
    >> fs [evaluate_decls_def]
    >> simp [compile_shape_eq, EVERY_MAP, UNCURRY]
    >> fs [EVERY_MEM, compile_shape_eq, UNCURRY, last (RES_CANON MAP_EQ_ID)]
    >> fs [FMAP_MAP2_FUPDATE]
    >> first_x_assum irule
    >> fs [code_rel_def, FLOOKUP_UPDATE]
    >> rw []
    >> metis_tac []
  )
QED

Theorem semantics_stcnames_get_names_none:
  !s decs. evaluate_stcnames s decs = SOME s' ==>
  get_names ctxt decs = ctxt
Proof
  recInduct (name_ind_cases [] evaluate_stcnames_ind)
  >> rw [evaluate_stcnames_def, get_names_def]
  >> fs [named_structs_ok_def, option_case_eq]
QED

Theorem semantics_stcnames_compile:
  !s decs ctxt. evaluate_stcnames s decs = SOME s' ==>
  evaluate_stcnames s (FST (compile_decs ctxt decs)) = SOME s' /\
  s' = s
Proof
  recInduct (name_ind_cases [] evaluate_stcnames_ind)
  >> rw [evaluate_stcnames_def, compile_decs_def, UNCURRY]
  >> fs [named_structs_ok_def, option_case_eq]
QED

(* copied from crep_to_loop. TODO: put somewhere useful *)
Datatype:
  semantics_run_res =
    RunError | CompleteResult 'a | Incomplete
End

Definition semantics_wrapper_def:
  semantics_wrapper f = (if ?k v. f k = (RunError, v) then Fail
    else case some res. ?k r ev. f k = (CompleteResult r, ev) /\ res = Terminate r ev
      of SOME res => res
        | NONE => Diverge (LUB (IMAGE (fromList o SND o f) (UNIV : num set))))
End

Theorem semantics_wrapper_eq:
  semantics_wrapper absf <> Fail ==>
  (! k r ev. absf k = (r, ev) /\ r <> RunError ==>
    ?k'. concf (k + k') = (r, ev)) ==>
  (!k k' r ev. concf k = (r, ev) ==>
    r <> Incomplete ==>
    concf (k + k') = (r, ev)) ==>
  (!k k' r ev. absf k = (r, ev) ==>
    r <> Incomplete ==>
    absf (k + k') = (r, ev)) ==>
  (!k k' ev. absf (k + k') = (Incomplete, ev) ==>
    ?r' ev'. absf k = (r', ev') /\ IS_PREFIX ev ev') ==>
  (!k k' ev. concf (k + k') = (Incomplete, ev) ==>
    ?r' ev'. concf k = (r', ev') /\ IS_PREFIX ev ev') ==>
  semantics_wrapper concf = semantics_wrapper absf
Proof
  rw []
  \\ Cases_on `semantics_wrapper absf` \\ fs []
  >- (
    fs [semantics_wrapper_def, CaseEq "bool"]
    \\ pop_assum mp_tac
    \\ DEEP_INTRO_TAC some_intro \\ simp []
    \\ disch_tac
    \\ reverse (qsuff_tac `?abs2. absf = (\k. (Incomplete, abs2 k))`)
    >- (
      qexists_tac `SND o absf`
      \\ rw [FUN_EQ_THM]
      \\ Cases_on `FST (absf k)` \\ Cases_on `absf k` \\ gs []
    )
    \\ strip_tac \\ fs []
    \\ reverse (qsuff_tac `?conc2. concf = (\k. (Incomplete, conc2 k))`)
    >- (
      qexists_tac `SND o concf`
      \\ rw [FUN_EQ_THM]
      \\ last_x_assum (qspec_then `k` mp_tac)
      \\ strip_tac
      \\ last_x_assum (qspecl_then [`k`, `k'`] mp_tac)
      \\ simp []
      \\ simp [PAIR_FST_SND_EQ]
    )
    \\ rw [] \\ fs []
    \\ qmatch_abbrev_tac `build_lprefix_lub l1 = build_lprefix_lub l2`
    \\ `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
      suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub]
    \\ conj_asm1_tac
    >- (
      UNABBREV_ALL_TAC
      \\ conj_tac
      \\ REWRITE_TAC[IMAGE_COMPOSE]
      \\ match_mp_tac prefix_chain_lprefix_chain
      \\ simp [prefix_chain_def, PULL_EXISTS]
      \\ qx_genl_tac [‘k1’, ‘k2’]
      \\ qspecl_then [‘k1’, ‘k2’] mp_tac LESS_EQ_CASES
      \\ simp[LESS_EQ_EXISTS]
      \\ rw []
      \\ metis_tac [ADD_COMM]
    )
    \\ simp [equiv_lprefix_chain_thm]
    \\ UNABBREV_ALL_TAC
    \\ simp[LNTH_fromList,PULL_EXISTS]
    \\ conj_tac
    >- (
      rw []
      \\ last_x_assum (qspec_then `x'` mp_tac)
      \\ strip_tac
      \\ pop_assum (assume_tac o GSYM)
      \\ qexists_tac `x'`
      \\ fs []
      \\ metis_tac [IS_PREFIX_THM, LESS_LESS_EQ_TRANS, ADD_COMM]
    )
    >- (
      rw []
      \\ metis_tac []
    )
  )
  \\ fs [semantics_wrapper_def, CaseEq "bool", CaseEq "option"]
  \\ pop_assum mp_tac
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ strip_tac
  \\ last_x_assum drule
  \\ simp [] \\ strip_tac
  \\ rename [`concf a_k = _`]
  \\ qsuff_tac `!k2 r v. concf k2 = (r, v) ==> (r, v) = concf a_k \/ (r = Incomplete)`
  >- (
    simp []
    \\ disch_tac
    \\ DEEP_INTRO_TAC some_intro \\ simp []
    \\ rw [] \\ fsrw_tac [SATISFY_ss] []
    \\ CCONTR_TAC \\ fs [] \\ res_tac \\ fs []
  )
  \\ rw []
  \\ qspecl_then [`a_k`, `k2`] mp_tac LESS_EQ_CASES
  \\ simp [LESS_EQ_EXISTS] \\ strip_tac \\ fs []
  \\ res_tac \\ fs []
  \\ rw [] \\ res_tac \\ fs []
  \\ CCONTR_TAC \\ fs []
  \\ res_tac \\ full_simp_tac bool_ss []
  \\ gs []
QED

Theorem pan_sem_is_wrapper:
  panSem$semantics s start =
  let prog = TailCall start [] in
  semantics_wrapper (((\res. case res of
    | SOME TimeOut => Incomplete
    | SOME (FinalFFI e) => CompleteResult (FFI_outcome e)
    | SOME (Return _) => CompleteResult Success
    | _ => RunError) ## (\s. s.ffi.io_events)) o
    (\k. evaluate (prog, s with clock := k)))
Proof
  simp [panSemTheory.semantics_def, semantics_wrapper_def]
  \\ irule COND_CONG
  \\ rw []
  >- (
    ho_match_mp_tac ConseqConvTheory.exists_eq_thm>>
    strip_tac>>
    simp[totoTheory.SPLIT_PAIRS,AllCasePreds()]>>
    simp[AllCaseEqs()]
  )
  >- (
    irule optionTheory.option_case_cong
    \\ simp [o_DEF]
    \\ (* both "some" *) AP_TERM_TAC
    \\ rw [FUN_EQ_THM]
    \\ ho_match_mp_tac ConseqConvTheory.exists_eq_thm
    \\ rw [] \\ EQ_TAC \\ rw []
    \\ every_case_tac \\ fs []
  )
QED

Theorem semantics_eq:
  semantics s start <> Fail ∧
  code_rel s.code code ∧
  ctxt.structs = [] ∧ s.structs = [] ∧
  FEVERY (λ(nm,v). is_wf_shape_v_nil v) s.locals ∧
  FEVERY (λ(nm,v). is_wf_shape_v_nil v) s.globals ==>
  semantics (s with code := code) start = semantics s start
Proof
  rw []
  >> fs [pan_sem_is_wrapper]
  >> drule_then irule semantics_wrapper_eq
  >> csimp []
  >> rw []
  >> TRY (
    rename [`option_CASE res _ _ <> Incomplete`] >>
    Cases_on `res = SOME TimeOut` >> fs []
  )
  >- (
    gvs [PAIR_FST_SND_EQ] >>
    irule isPREFIX_TRANS >>
    irule_at Any evaluate_add_clock_io_events_mono >>
    simp [] >>
    metis_tac [ADD_COMM, isPREFIX_REFL]
  )
  >- (
    gvs [PAIR_FST_SND_EQ] >>
    irule isPREFIX_TRANS >>
    irule_at Any evaluate_add_clock_io_events_mono >>
    simp [] >>
    metis_tac [ADD_COMM, isPREFIX_REFL]
  )
  >- (
    drule panPropsTheory.evaluate_add_clock_eq >>
    simp [] >>
    (* ugh at renaming a variable so it sorts to the right *)
    disch_then (qspec_then `x` (mp_tac o Q.GEN `x`)) >>
    simp []
  )
  >- (
    drule panPropsTheory.evaluate_add_clock_eq >>
    simp [] >>
    (* ugh at renaming a variable so it sorts to the right *)
    disch_then (qspec_then `x` (mp_tac o Q.GEN `x`)) >>
    simp []
  )
  >- (
    qexists_tac `0` >>
    drule compile_correct >>
    simp [compile_def, compile_exp_def] >>
    disch_then drule >>
    impl_tac >> strip_tac >> fs []
  )
QED

Theorem evaluate_decls_invariant:
  !s code. evaluate_decls s code = SOME s' /\
  s.locals = FEMPTY /\
  s.structs = [] ==>
  s'.structs = [] /\
  s'.locals = FEMPTY /\
  (FEVERY (λ(nm,v). is_wf_shape_v_nil v) s.globals ==>
    FEVERY (λ(nm,v). is_wf_shape_v_nil v) s'.globals)
Proof
  recInduct evaluate_decls_ind
  >> simp [evaluate_decls_def]
  >> rw []
  >> fs [option_case_eq]
  >> drule eval_is_wf_shape_v
  >> fs []
  >> rw [FEVERY_FEMPTY]
  >> first_x_assum irule
  >> simp [FEVERY_FUPDATE, fevery_to_drestrict]
QED

Theorem compile_top_semantics_decls:
  semantics_decls s start code <> Fail ∧
  s.structs = [] ∧ s.locals = FEMPTY ∧ s.code = FEMPTY ∧
  s.globals = FEMPTY ⇒
  semantics_decls s start code =
  semantics_decls s start (compile_top code)
Proof
  rw [semantics_decls_def]
  >> TOP_CASE_TAC >> fs []
  >> TOP_CASE_TAC >> fs []
  >> imp_res_tac semantics_stcnames_get_names_none
  >> imp_res_tac semantics_stcnames_compile
  >> simp [compile_top_def]
  >> qmatch_goalsub_abbrev_tac `compile_decs nm_ctxt`
  >> drule_then (qspecl_then [`nm_ctxt`, `FEMPTY`] mp_tac) compile_decs_correct
  >> fs [markerTheory.Abbrev_def]
  >> simp [FEVERY_FEMPTY, Q.SPEC `FEMPTY` code_rel_def]
  >> rw []
  >> subgoal `(s with code := FEMPTY) = s` >- ( simp [state_component_equality] )
  >> fs []
  >> irule (GSYM semantics_eq)
  >> simp []
  >> imp_res_tac evaluate_decls_invariant
  >> gs [FEVERY_FEMPTY]
  >> qexists_tac `ARB with structs := []`
  >> simp []
QED

Theorem compile_top_no_names:
  EVERY (λd. is_function d ∨ is_decl d) (pan_structs$compile_top pan_code)
Proof
  cheat
QED


