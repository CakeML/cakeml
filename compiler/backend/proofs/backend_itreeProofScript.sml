(*
  Compiler correctness for the itree CakeML semantics
*)
Theory backend_itreeProof
Ancestors
  semanticsProps evaluateProps ffi targetProps lab_to_targetProof
  backendProof primSemEnv alt_semantics target_itreeSem
  target_itreeProps target_itreeEquiv itree_semantics
  itree_semanticsProps itree_semanticsEquiv
Libs
  preamble

(*********** Definitions **********)

CoInductive prune:
  prune P exact Div                          Div                  ∧
  prune P exact (Ret Termination)            (Ret Termination)    ∧
  prune P exact (Ret itree_semantics$Error)  (Ret Error)          ∧
  prune P F     t                            (Ret OutOfMemory)    ∧
  prune P exact (Ret (FinalFFI x y))         (Ret (FinalFFI x y)) ∧
  ((∀x. P x ⇒ prune P exact (f x) (g x)) ⇒ prune P exact (Vis d f) (Vis d g))
End

Definition same_up_to_oom_def:
  (same_up_to_oom exact a b ys ⇔
     (a = Div ∧ b = Div) ∨
     (a = Ret Termination ∧ b = Ret Termination) ∨
     (a = Ret (itree_semantics$Error) ∧ b = Ret Error) ∨
     (¬exact ∧ b = Ret OutOfMemory) ∨
     (∃x y. a = Ret (FinalFFI x y) ∧ b = Ret (FinalFFI x y)) ∨
     ∃d f g.
       a = Vis d f ∧ b = Vis d g ∧
       case ys of [] => T | x::xs => same_up_to_oom exact (f x) (g x) xs)
End

Definition bisimilar_up_to_oom_def:
  bisimilar_up_to_oom exact P a b = ∀xs. EVERY P xs ⇒ same_up_to_oom exact a b xs
End

Definition list_oracle_def:
  list_oracle name [] bytes1 bytes2 = Oracle_final FFI_diverged ∧
  list_oracle name (INR x::rest) bytes1 bytes2 = Oracle_return rest x ∧
  list_oracle name (INL l::rest) bytes1 bytes2 = Oracle_final l
End

Definition make_ffi_def:
  make_ffi xs = <|
       io_events := [] ;
       ffi_state := xs ;
       oracle := list_oracle
     |>
End

Inductive trace_rel:
  trace_rel exact (io, NONE) (io, NONE) ∧

  trace_rel exact (io, SOME itree_semantics$Termination) (io, SOME Termination) ∧
  trace_rel exact (io, SOME $ FinalFFI e r) (io, SOME $ FinalFFI e r) ∧

  (isPREFIX io' io ⇒
    trace_rel F (io, res) (io', SOME OutOfMemory))
End

CoInductive ffi_invariant:
  ((∀e input. x ≠ f e input) ⇒ ffi_invariant f (Ret x)) ∧
  ffi_invariant f Div ∧
  ((∀outcome. g (INL outcome) = Ret $ f e outcome) ∧
   (∀input. LENGTH input ≠ LENGTH (SND $ SND e) ⇒ g (INR input) = Ret $ f e FFI_failed) ∧
   (∀input. LENGTH input = LENGTH (SND $ SND e) ⇒ ffi_invariant f (g (INR input)))
      ⇒ ffi_invariant f (Vis e g))
End

CoInductive ffi_respects_convention:
  (∀s ws1 ws2 st' ws final.
    (f s st ws1 ws2 = Oracle_return st' ws ⇒
      P (INR ws) ∧ ffi_respects_convention P (f,st')) ∧
    (f s st ws1 ws2 = Oracle_final final ⇒ P (INL final)))
  ⇒ ffi_respects_convention P (f,st)
End


(*********** Lemmas **********)

Theorem prune_eq_bisimilar_up_to_oom:
  bisimilar_up_to_oom exact P a b ⇔ prune P exact a b
Proof
  eq_tac >> rw[]
  >- (
    pop_assum mp_tac >> map_every qid_spec_tac [`b`,`a`,`exact`] >>
    ho_match_mp_tac prune_coind >> rw[bisimilar_up_to_oom_def] >>
    first_assum $ qspec_then `[]` assume_tac >> fs[Once same_up_to_oom_def] >> rw[] >>
    first_x_assum $ qspec_then `x::xs` mp_tac >> simp[] >> simp[Once same_up_to_oom_def]
    )
  >- (
    rw[bisimilar_up_to_oom_def] >>
    ntac 2 $ pop_assum mp_tac >> map_every qid_spec_tac [`b`,`a`,`xs`] >>
    Induct >> rw[Once same_up_to_oom_def] >>
    qpat_x_assum `prune _ _ _ _` mp_tac >> rw[Once prune_cases]
    )
QED

Triviality make_ffi_simps[simp]:
  (make_ffi l).oracle = list_oracle ∧
  (make_ffi l).io_events = [] ∧
  (make_ffi l).ffi_state = l
Proof
  rw[make_ffi_def]
QED

Triviality list_oracle_apply =
  SIMP_CONV (srw_ss()) [DefnBase.one_line_ify NONE list_oracle_def]
    ``list_oracle name l ws1 ws2``;

Triviality trace_rel_simps[simp] =
  trace_rel_rules |> CONJUNCTS |> butlast |> LIST_CONJ;

Triviality trace_rel_prefix:
  trace_rel exact a b ⇒ isPREFIX (FST b) (FST a)
Proof
  rw[trace_rel_cases] >> simp[]
QED

Theorem trace_rel_CONS:
  trace_rel exact (io1::ios1, res1) (io2::ios2, res2) ⇔
  io1 = io2 ∧ trace_rel exact (ios1, res1) (ios2, res2)
Proof
  eq_tac >> simp[] >>
  Induct_on `trace_rel` >> rw[] >> gvs[trace_rel_cases, IS_PREFIX]
QED

Triviality ffi_invariant_simps[simp]:
  ffi_invariant f (Ret x) = (∀e input. x ≠ f e input) ∧
  ffi_invariant f Div = T ∧
  ffi_invariant f (Vis e g) = (
     (∀outcome. g (INL outcome) = Ret (f e outcome)) ∧
     (∀input.
        LENGTH input ≠ LENGTH (SND (SND e)) ⇒
        g (INR input) = Ret (f e FFI_failed)) ∧
     ∀input.
       LENGTH input = LENGTH (SND (SND e)) ⇒
       ffi_invariant f (g (INR input)))
Proof
  rw[] >> simp[Once ffi_invariant_cases]
QED

Theorem ffi_invariant_itree_of:
  ffi_invariant FinalFFI (itree_of st env prog)
Proof
  rw[itree_of_def] >>
  `∀t. (∃env e. t = interp env e) ⇒ ffi_invariant FinalFFI t`
    suffices_by rw[PULL_EXISTS] >>
  ho_match_mp_tac ffi_invariant_coind >> rw[] >>
  Cases_on `interp env e` >> rw[] >>
  gvs[Once interp] >> every_case_tac >> gvs[] >> irule_at Any EQ_REFL
QED

Theorem ffi_invariant_machine_sem_itree:
  ffi_invariant FinalFFI (machine_sem_itree (mc,ms))
Proof
  rw[] >>
  `∀t. (∃mc ms. t = machine_sem_itree (mc,ms)) ⇒ ffi_invariant FinalFFI t`
    suffices_by rw[PULL_EXISTS] >>
  ho_match_mp_tac ffi_invariant_coind >> rw[] >>
  Cases_on `machine_sem_itree (mc,ms)` >> rw[] >>
  gvs[Once machine_sem_itree] >> every_case_tac >> gvs[]
  >- (
    CCONTR_TAC >> gvs[eval_alt_def, AllCaseEqs()] >>
    pairarg_tac >> gvs[eval_to'_Ret_FinalFFI]
    )
  >- (Cases_on `f input` >> irule_at Any EQ_REFL)
QED

Theorem extend_no_oom:
  extend_with_resource_limit' exact behaviours behaviour ∧
  (∀io. behaviour ≠ Terminate Resource_limit_hit io) ⇒
  behaviours behaviour
Proof
  rw[extend_with_resource_limit'_def, extend_with_resource_limit_def] >>
  gvs[IN_DEF]
QED

Theorem safe_itree_trace_prefix_Error:
  ∀n P ffi io t.
    ffi_respects_convention P ffi ∧
    safe_itree P t
  ⇒ trace_prefix n ffi t ≠ (io, SOME Error)
Proof
  Induct >> rw[] >> PairCases_on `ffi` >> gvs[] >>
  simp[trace_prefix_def] >> Cases_on `t` >> gvs[trace_prefix_def] >>
  pop_assum mp_tac >> rw[Once safe_itree_cases] >>
  PairCases_on `a` >> simp[trace_prefix_def] >> reverse CASE_TAC >> gvs[]
  >- (
    first_x_assum $ qspec_then `INL f` assume_tac >> gvs[] >>
    qsuff_tac `P (INL f)` >- (rw[] >> gvs[] >> metis_tac[]) >>
    qpat_x_assum `ffi_respects_convention _ _` mp_tac >>
    rw[Once ffi_respects_convention_cases] >> res_tac >> gvs[]
    ) >>
  pairarg_tac >> gvs[] >> qsuff_tac `res ≠ SOME Error` >> rw[] >> gvs[] >>
  first_x_assum $ qspec_then `INR l` assume_tac >> gvs[] >>
  qpat_x_assum `ffi_respects_convention _ _` mp_tac >>
  rw[Once ffi_respects_convention_cases] >> res_tac >> gvs[] >>
  first_x_assum $ qspecl_then [`P`,`ffi0,f`,`io'`,`g (INR l)`] assume_tac >> gvs[]
QED


(*********** Theorems **********)

Theorem trace_rel_IMP_bisimilar_up_to_oom:
  ∀exact ffi_st src trgt.
    ffi_invariant FinalFFI src ∧
    ffi_invariant FinalFFI trgt ∧
    EVERY P ffi_st ∧
    (∀n.
      trace_rel exact
        (trace_prefix n (list_oracle, ffi_st) src)
        (trace_prefix n (list_oracle, ffi_st) trgt))
  ⇒ same_up_to_oom exact src trgt ffi_st
Proof
  gen_tac >> Induct >>
  rw[Once same_up_to_oom_def] >>
  Cases_on `trgt = Ret OutOfMemory` >> gvs[]
  >- (
    CCONTR_TAC >> gvs[] >>
    first_x_assum $ qspec_then `SUC n` mp_tac >>
    simp[trace_prefix_def, Once trace_rel_cases]
    )
  >- (
    reverse $ Cases_on `src` >> gvs[] >>
    first_x_assum $ qspec_then `SUC n` $ mp_tac o GEN_ALL >>
    gvs[trace_prefix_def, trace_rel_cases] >>
    reverse $ Cases_on `trgt` >> gvs[trace_prefix_def] >>
    PairCases_on `a` >> gvs[trace_prefix_def, list_oracle_apply]
    >- (
      PairCases_on `a'` >> gvs[] >>
      disch_then $ qspec_then `SUC n` mp_tac >>
      gvs[trace_prefix_def, list_oracle_apply]
      ) >>
    qrefine `SUC n` >> gvs[trace_prefix_def]
    )
  >- (
    CCONTR_TAC >> gvs[] >>
    first_x_assum $ qspec_then `SUC n` mp_tac >>
    simp[trace_prefix_def, Once trace_rel_cases]
    ) >>
  Cases_on `src` >> gvs[]
  >- ( (* Ret *)
    first_x_assum $ qspec_then `SUC n` $ mp_tac o GEN_ALL >>
    simp[trace_prefix_def, trace_rel_cases] >>
    Cases_on `trgt` >> gvs[trace_prefix_def] >>
    PairCases_on `a` >> simp[trace_prefix_def, list_oracle_apply] >>
    CASE_TAC >> simp[] >> qexists_tac `SUC n` >> simp[trace_prefix_def] >>
    Cases_on `LENGTH a2 = LENGTH y` >> gvs[UNCURRY, trace_prefix_def]
    )
  >- ( (* Div *)
    first_x_assum $ qspec_then `SUC n` $ mp_tac o GEN_ALL >>
    simp[trace_prefix_def, trace_rel_cases] >>
    Cases_on `trgt` >> gvs[trace_prefix_def] >>
    PairCases_on `a` >> simp[trace_prefix_def, list_oracle_apply] >>
    CASE_TAC >> simp[] >> qexists_tac `SUC n` >> simp[trace_prefix_def] >>
    Cases_on `LENGTH a2 = LENGTH y` >> gvs[UNCURRY, trace_prefix_def]
    )
  >- ( (* Vis *)
    first_x_assum $ qspec_then `SUC n` $ assume_tac o GEN_ALL >>
    PairCases_on `a` >> gvs[trace_prefix_def, list_oracle_apply] >>
    Cases_on `h` >> gvs[]
    >- (
      pop_assum $ qspec_then `SUC n` $ mp_tac o GEN_ALL >>
      simp[trace_prefix_def, Once trace_rel_cases] >>
      Cases_on `trgt` >> simp[trace_prefix_def] >> gvs[] >>
      PairCases_on `a` >> simp[trace_prefix_def, list_oracle_apply] >>
      rw[] >> gvs[] >> Cases_on `ffi_st` >> simp[Once same_up_to_oom_def]
      ) >>
    reverse $ Cases_on `LENGTH a2 = LENGTH y` >> gvs[]
    >- (
      first_x_assum $ qspec_then `SUC n` $ mp_tac o GEN_ALL >>
      simp[trace_prefix_def, trace_rel_cases] >>
      Cases_on `trgt` >> gvs[trace_prefix_def] >>
      PairCases_on `a` >> simp[trace_prefix_def, list_oracle_apply, UNCURRY] >>
      strip_tac >> `LENGTH a2' ≠ LENGTH y` by (CCONTR_TAC >> gvs[]) >> gvs[] >>
      Cases_on `ffi_st` >> simp[Once same_up_to_oom_def]
      ) >>
    first_x_assum $ qspec_then `SUC n` $ mp_tac o GEN_ALL >>
    Cases_on `trgt` >> gvs[]
    >- (
      simp[trace_prefix_def, trace_rel_cases] >>
      qexists_tac `0` >> pairarg_tac >> gvs[]
      )
    >- (
      simp[trace_prefix_def, trace_rel_cases] >>
      qexists_tac `0` >> pairarg_tac >> gvs[]
      ) >>
    PairCases_on `a` >> gvs[trace_prefix_def, list_oracle_apply, UNCURRY] >>
    strip_tac >>
    `LENGTH a2' = LENGTH y` by (
      CCONTR_TAC >> gvs[] >> first_x_assum $ qspec_then `SUC n` mp_tac >>
      simp[trace_prefix_def, trace_rel_cases]) >>
    conj_asm1_tac
    >- (
      first_x_assum $ qspec_then `n` assume_tac >>
      imp_res_tac trace_rel_prefix >> gvs[LIST_EQ_REWRITE, EL_ZIP]
      ) >>
    gvs[] >> last_x_assum irule >> rw[] >>
    Cases_on `n` >> simp[trace_prefix_def] >>
    first_x_assum $ qspec_then `n'` assume_tac >> gvs[trace_rel_CONS]
    )
QED

Overload inr = ``λP. SUM_ALL (K T) P``

Theorem oracle_IMP_itree_preservation:
  s.eval_state = NONE ∧
  (∀f:(((ffi_outcome + word8 list) list) ffi_state).
    ffi_respects_convention (inr P) (f.oracle, f.ffi_state) ⇒
    Fail ∉ semantics_prog (s with ffi := f) env prog ∧
    machine_sem (mc:(α,β,γ) machine_config) f ms ⊆
      extend_with_resource_limit' safe_for_space
        (semantics_prog (s with ffi := f) env prog))
  ⇒ prune (inr P) safe_for_space (itree_of s env prog) (machine_sem_itree (mc,ms))
Proof
  rw[GSYM prune_eq_bisimilar_up_to_oom, bisimilar_up_to_oom_def] >>
  first_x_assum $ qspec_then `make_ffi xs` assume_tac >> gvs[GSYM PULL_FORALL] >>
  pop_assum mp_tac >> impl_tac
  >- (
    Induct_on `xs` >> rw[Once ffi_respects_convention_cases, list_oracle_apply] >>
    gvs[AllCaseEqs()]
    ) >>
  strip_tac >> gvs[] >>
  irule trace_rel_IMP_bisimilar_up_to_oom >> simp[SF SFY_ss] >> reverse conj_asm2_tac
  >- simp[ffi_invariant_itree_of, ffi_invariant_machine_sem_itree] >>
  qabbrev_tac `st = s with ffi := make_ffi xs` >>
  `st.eval_state = NONE` by (unabbrev_all_tac >> gvs[]) >> last_x_assum kall_tac >>
  `∀n io. trace_prefix n (list_oracle,xs) (itree_of st env prog) ≠ (io, SOME Error)`
    by (
      drule $ cj 3 itree_semantics >>
      disch_then $ qspecl_then [`prog`,`env`] assume_tac >>
      unabbrev_all_tac >> gvs[IN_DEF]) >>
  qpat_x_assum `Fail ∉ _` kall_tac >>
  qspecl_then [`make_ffi xs`,`ms`,`mc`] assume_tac $ GEN_ALL machine_sem_total >>
  gvs[SUBSET_DEF, IN_DEF] >> last_x_assum drule >> strip_tac >>
  qmatch_asmsub_abbrev_tac `trace_prefix _ _ src` >>
  qabbrev_tac `trgt = machine_sem_itree (mc,ms)` >>
  `itree_ffi st = (list_oracle,xs)` by (unabbrev_all_tac >> rw[]) >>
  gvs[] >> qabbrev_tac `xs = st.ffi.ffi_state` >> gvs[Abbr `st`] >>
  `itree_of s env prog = src` by (
    unabbrev_all_tac >> gvs[itree_of_def, dstate_of_def]) >>
  pop_assum SUBST_ALL_TAC >>
  Cases_on `b` >> imp_res_tac extend_no_oom >>
  gvs[itree_semantics, itree_machine_semantics] >>
  qpat_x_assum `∀n io. _ ≠ _` kall_tac
  >- (
    qpat_x_assum `extend_with_resource_limit' _ _ _` kall_tac >>
    qpat_x_assum `_ = NONE `kall_tac >> rpt $ qpat_x_assum `Abbrev _` kall_tac >>
    gen_tac >> rpt $ pop_assum mp_tac >>
    map_every qid_spec_tac [`l`,`trgt`,`src`,`xs`,`n`] >>
    Induct >> rw[trace_prefix_def] >>
    ntac 2 $ last_x_assum $ qspec_then `SUC n` $ assume_tac o GEN_ALL >>
    Cases_on `src` >> gvs[trace_prefix_def]
    >- (
      last_x_assum kall_tac >> gvs[PULL_EXISTS] >>
      simp[trace_rel_cases] >> disj1_tac >> metis_tac[]
      ) >>
    Cases_on `trgt` >> gvs[trace_prefix_def, PULL_EXISTS]
    >- (
      PairCases_on `a` >> gvs[trace_prefix_def, list_oracle_apply] >>
      CASE_TAC >> gvs[]
      >- (first_x_assum $ qspec_then `SUC n` mp_tac >> simp[trace_prefix_def]) >>
      CASE_TAC >> gvs[]
      >- (first_x_assum $ qspec_then `SUC n` mp_tac >> simp[trace_prefix_def]) >>
      qpat_x_assum `∀io n' res. _ ⇒ io = []` mp_tac >> simp[Once SWAP_FORALL_THM] >>
      disch_then $ qspec_then `SUC n` $ mp_tac >>
      simp[trace_prefix_def, list_oracle_apply] >>
      reverse $ CASE_TAC >> gvs[] >> pairarg_tac >> simp[] >>
      first_x_assum $ qspec_then `n` assume_tac >> gvs[]
      ) >>
    PairCases_on `a` >> PairCases_on `a'` >>
    gvs[trace_prefix_def, list_oracle_apply] >> CASE_TAC >> gvs[]
    >- (first_x_assum $ qspec_then `SUC n` mp_tac >> simp[trace_prefix_def]) >>
    CASE_TAC >> gvs[]
    >- (first_x_assum $ qspec_then `SUC n` mp_tac >> simp[trace_prefix_def]) >>
    CASE_TAC >> gvs[] >> CASE_TAC >> gvs[]
    >- (first_x_assum $ qspec_then `SUC n` mp_tac >> simp[trace_prefix_def])
    >- (first_x_assum $ qspec_then `SUC n` mp_tac >> simp[trace_prefix_def])
    >- (last_x_assum $ qspec_then `SUC n` mp_tac >> simp[trace_prefix_def]) >>
    simp[UNCURRY, trace_rel_CONS] >> Cases_on `l` >> gvs[PULL_EXISTS]
    >- (
      irule FALSITY >> qpat_x_assum `∀io n res. _` mp_tac >> simp[] >>
      simp[Once SWAP_EXISTS_THM] >> qexists_tac `SUC n` >>
      simp[trace_prefix_def, list_oracle_apply] >> pairarg_tac >> simp[]
      ) >>
    conj_asm1_tac >> gvs[]
    >- (
      imp_res_tac lprefix_lub_LCONS >> gvs[PULL_EXISTS] >>
      ntac 2 $ pop_assum mp_tac >>
      ntac 2 (simp[Once SWAP_FORALL_THM] >>
              disch_then $ qspec_then `SUC n` assume_tac) >>
      gvs[trace_prefix_def, list_oracle_apply] >> ntac 2 (pairarg_tac >> gvs[])
      ) >>
    last_x_assum irule >> rw[]
    >- (
      ntac 2 $ first_x_assum $ qspec_then `n` assume_tac >> rpt (pairarg_tac >> gvs[])
      )
    >- (
      ntac 2 $ first_x_assum $ qspec_then `n` assume_tac >> rpt (pairarg_tac >> gvs[])
      ) >>
    qexists_tac `t'` >> rw[]
    >- (
      irule lprefix_lub_LTL >> goal_assum $ drule_at Any >>
      rw[PULL_EXISTS, LTL_fromList, EXTENSION] >> eq_tac >> rw[]
      >- (
        simp[Once SWAP_EXISTS_THM] >> qexists_tac `SUC n` >>
        simp[trace_prefix_def, list_oracle_apply]
        )
      >- (
        Cases_on `n'` >> gvs[trace_prefix_def, list_oracle_apply] >>
        pairarg_tac >> gvs[SF SFY_ss]
        )
      )
    >- (
      irule lprefix_lub_LTL >> goal_assum $ rev_drule_at Any >>
      rw[PULL_EXISTS, LTL_fromList, EXTENSION] >> eq_tac >> rw[]
      >- (
        simp[Once SWAP_EXISTS_THM] >> qexists_tac `SUC n` >>
        simp[trace_prefix_def, list_oracle_apply]
        )
      >- (
        Cases_on `n` >> gvs[trace_prefix_def, list_oracle_apply] >>
        pairarg_tac >> gvs[SF SFY_ss]
        )
      )
    ) >>
  rename1 `outcome = Success` >>
  reverse $ Cases_on `outcome = Resource_limit_hit` >> gvs[]
  >- (
    rename1 `trace_prefix m _ _ = (_, SOME res)` >>
    rename1 `trace_prefix m' _ _ = (_, SOME res')` >>
    qpat_x_assum `extend_with_resource_limit' _ _ _` kall_tac >>
    qpat_x_assum `_ = NONE `kall_tac >> rpt $ qpat_x_assum `Abbrev _` kall_tac >>
    gen_tac >> rpt $ pop_assum mp_tac >>
    map_every qid_spec_tac [`l`,`m`,`trgt`,`m'`,`src`,`xs`,`n`] >>
    Induct >> rw[trace_prefix_def]
    >- (
      Cases_on `m` >> gvs[trace_prefix_def] >>
      Cases_on `m'` >> gvs[trace_prefix_def] >>
      Cases_on `src` >> gvs[trace_prefix_def] >>
      Cases_on `trgt` >> gvs[trace_prefix_def]
      >- (
        PairCases_on `a` >> gvs[trace_prefix_def, AllCaseEqs()] >>
        rpt (pairarg_tac >> gvs[]) >> every_case_tac >> gvs[] >>
        Cases_on `n'` >> gvs[trace_prefix_def]
        )
      >- (
        PairCases_on `a` >> gvs[trace_prefix_def, AllCaseEqs()] >>
        rpt (pairarg_tac >> gvs[]) >> every_case_tac >> gvs[] >>
        Cases_on `n''` >> gvs[trace_prefix_def]
        ) >>
      PairCases_on `a` >> PairCases_on `a'` >>
      gvs[trace_prefix_def, list_oracle_apply] >>
      CASE_TAC >> gvs[] >- (Cases_on `n'` >> gvs[trace_prefix_def]) >>
      CASE_TAC >> gvs[] >- (Cases_on `n'` >> gvs[trace_prefix_def]) >>
      CASE_TAC >> gvs[] >- (Cases_on `n''` >> gvs[trace_prefix_def]) >>
      CASE_TAC >> gvs[] >- (Cases_on `n'` >> gvs[trace_prefix_def]) >>
      simp[UNCURRY, trace_rel_CONS] >>
      conj_asm1_tac >- rpt (pairarg_tac >> gvs[]) >> gvs[] >>
      first_x_assum irule >> simp[] >> rpt (pairarg_tac >> gvs[]) >> simp[SF SFY_ss]
      )
    >- (
      Cases_on `m` >> gvs[trace_prefix_def] >>
      Cases_on `m'` >> gvs[trace_prefix_def] >>
      Cases_on `src` >> gvs[trace_prefix_def] >>
      Cases_on `trgt` >> gvs[trace_prefix_def] >>
      PairCases_on `a` >> PairCases_on `a'` >>
      gvs[trace_prefix_def, list_oracle_apply] >>
      CASE_TAC >> gvs[]
      >- (map_every Cases_on [`n`,`n'`,`n''`] >> gvs[trace_prefix_def]) >>
      CASE_TAC >> gvs[]
      >- (map_every Cases_on [`n`,`n'`,`n''`] >> gvs[trace_prefix_def]) >>
      rpt (pairarg_tac >> gvs[]) >>
      `IO_event a'0 a'1 (ZIP (a'2,y)) = IO_event a0 a1 (ZIP (a2,y))` by (
        every_case_tac >> gvs[] >>
        Cases_on `n'` >> Cases_on `n''` >> gvs[trace_prefix_def]) >>
      CASE_TAC >> gvs[] >> CASE_TAC >> gvs[]
      >- (map_every Cases_on [`n`,`n'`,`n''`] >> gvs[trace_prefix_def])
      >- (map_every Cases_on [`n`,`n'`,`n''`] >> gvs[trace_prefix_def])
      >- (map_every Cases_on [`n`,`n'`,`n''`] >> gvs[trace_prefix_def]) >>
      simp[trace_rel_CONS] >>
      first_x_assum $ drule_at Any >> simp[] >> disch_then $ drule_at Any >> simp[]
      )
    ) >>
  gvs[extend_with_resource_limit'_def, extend_with_resource_limit_def] >>
  gvs[COND_RATOR, IN_DEF, itree_semantics]
  >- (
    rename1 `trace_prefix m _ _ = (_, SOME res)` >>
    rename1 `trace_prefix m' _ _ = (_, SOME OutOfMemory)` >>
    qpat_x_assum `_ = NONE `kall_tac >> rpt $ qpat_x_assum `Abbrev _` kall_tac >>
    gen_tac >> rpt $ pop_assum mp_tac >>
    map_every qid_spec_tac [`l'`,`l`,`m`,`trgt`,`m'`,`src`,`xs`,`n`] >>
    Induct >> rw[trace_prefix_def]
    >- (
      Cases_on `m` >> gvs[trace_prefix_def] >>
      Cases_on `m'` >> gvs[trace_prefix_def] >>
      Cases_on `trgt` >> gvs[trace_prefix_def]
      >- (simp[trace_rel_cases] >> metis_tac[PAIR]) >>
      Cases_on `src` >> gvs[trace_prefix_def]
      >- (
        PairCases_on `a` >> gvs[trace_prefix_def, list_oracle_apply] >>
        rpt (CASE_TAC >> gvs[]) >> Cases_on `n''` >> gvs[trace_prefix_def] >>
        rpt (pairarg_tac >> gvs[])
        ) >>
      PairCases_on `a` >> PairCases_on `a'` >>
      gvs[trace_prefix_def, list_oracle_apply] >>
      CASE_TAC >> gvs[] >- (Cases_on `n'` >> gvs[trace_prefix_def]) >>
      CASE_TAC >> gvs[] >- (Cases_on `n'` >> gvs[trace_prefix_def]) >>
      CASE_TAC >> gvs[] >- (Cases_on `n'` >> gvs[trace_prefix_def]) >>
      CASE_TAC >> gvs[] >- (Cases_on `n''` >> gvs[trace_prefix_def]) >>
      simp[UNCURRY, trace_rel_CONS] >>
      conj_asm1_tac >- rpt (pairarg_tac >> gvs[]) >> gvs[] >>
      first_x_assum irule >> simp[] >> rpt (pairarg_tac >> gvs[]) >> simp[SF SFY_ss]
      )
    >- (
      Cases_on `m` >> gvs[trace_prefix_def] >>
      Cases_on `m'` >> gvs[trace_prefix_def] >>
      Cases_on `src` >> gvs[trace_prefix_def] >>
      Cases_on `trgt` >> gvs[trace_prefix_def]
      >- (simp[trace_rel_cases] >> metis_tac[PAIR]) >>
      PairCases_on `a` >> PairCases_on `a'` >>
      gvs[trace_prefix_def, list_oracle_apply] >>
      CASE_TAC >> gvs[]
      >- (map_every Cases_on [`n`,`n'`,`n''`] >> gvs[trace_prefix_def]) >>
      CASE_TAC >> gvs[]
      >- (map_every Cases_on [`n`,`n'`,`n''`] >> gvs[trace_prefix_def]) >>
      rpt (pairarg_tac >> gvs[]) >>
      `IO_event a'0 a'1 (ZIP (a'2,y)) = IO_event a0 a1 (ZIP (a2,y))` by (
        every_case_tac >> gvs[] >>
        Cases_on `n'` >> Cases_on `n''` >> gvs[trace_prefix_def]) >>
      gvs[] >> CASE_TAC >> gvs[] >> CASE_TAC >> gvs[]
      >- (map_every Cases_on [`n`,`n'`,`n''`] >> gvs[trace_prefix_def])
      >- (map_every Cases_on [`n`,`n'`,`n''`] >> gvs[trace_prefix_def])
      >- (map_every Cases_on [`n`,`n'`,`n''`] >> gvs[trace_prefix_def]) >>
      simp[trace_rel_CONS] >>
      first_x_assum $ drule_at Any >> simp[] >> disch_then $ drule_at Any >> simp[]
      )
    )
  >- (
    rename1 `trace_prefix m _ _ = (_, SOME OutOfMemory)` >>
    qpat_x_assum `_ = NONE `kall_tac >> rpt $ qpat_x_assum `Abbrev _` kall_tac >>
    gen_tac >> rpt $ pop_assum mp_tac >>
    map_every qid_spec_tac [`ll`,`l`,`m`,`trgt`,`src`,`xs`,`n`] >>
    Induct >> rw[trace_prefix_def] >>
    Cases_on `m` >> gvs[trace_prefix_def] >>
    Cases_on `trgt` >> gvs[trace_prefix_def]
    >- (simp[trace_rel_cases] >> metis_tac[PAIR]) >>
    first_x_assum $ qspec_then `SUC n` $ assume_tac o GEN_ALL >>
    Cases_on `src` >> gvs[trace_prefix_def]
    >- (
      PairCases_on `a` >> gvs[trace_prefix_def, AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs[]) >> every_case_tac >> gvs[] >>
      Cases_on `n'` >> gvs[trace_prefix_def]
      ) >>
    PairCases_on `a` >> PairCases_on `a'` >> gvs[trace_prefix_def, list_oracle_apply] >>
    CASE_TAC >> gvs[] >- (Cases_on `n'` >> gvs[trace_prefix_def]) >>
    CASE_TAC >> gvs[] >- (Cases_on `n'` >> gvs[trace_prefix_def]) >>
    CASE_TAC >> gvs[] >> CASE_TAC >> gvs[]
    >- (Cases_on `n'` >> gvs[trace_prefix_def])
    >- (first_x_assum $ qspec_then `SUC n` mp_tac >> simp[trace_prefix_def])
    >- (Cases_on `n'` >> gvs[trace_prefix_def]) >>
    simp[UNCURRY, trace_rel_CONS] >> Cases_on `ll` >> gvs[PULL_EXISTS]
    >- (
      irule FALSITY >> qpat_x_assum `∀io n res. _` mp_tac >> simp[] >>
      simp[Once SWAP_EXISTS_THM] >> qexists_tac `SUC n` >>
      simp[trace_prefix_def, list_oracle_apply] >> pairarg_tac >> simp[]
      ) >>
    conj_asm1_tac >> gvs[]
    >- (
      imp_res_tac lprefix_lub_LCONS >> gvs[PULL_EXISTS] >>
      pop_assum mp_tac >> simp[Once SWAP_FORALL_THM] >>
      disch_then $ qspec_then `SUC n'` mp_tac >>
      simp[trace_prefix_def, list_oracle_apply] >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[LPREFIX_LCONS]
      ) >>
    last_x_assum irule >> rw[]
    >- (first_x_assum $ qspec_then `n''` assume_tac >> pairarg_tac >> gvs[]) >>
    pairarg_tac >> gvs[LPREFIX_LCONS] >> rpt $ goal_assum drule >>
    irule lprefix_lub_LTL >> goal_assum $ drule_at Any >>
    rw[PULL_EXISTS, LTL_fromList, EXTENSION] >> eq_tac >> rw[]
    >- (
      simp[Once SWAP_EXISTS_THM] >> qexists_tac `SUC n''` >>
      simp[trace_prefix_def, list_oracle_apply]
      )
    >- (
      Cases_on `n''` >> gvs[trace_prefix_def, list_oracle_apply] >>
      pairarg_tac >> gvs[SF SFY_ss]
      )
    )
QED

Theorem itree_compile_correct:
  safe_itree (inr P) (itree_semantics prog) ∧
  compile c prog = SOME (bytes,bitmaps,c') ∧
  backend_config_ok c ∧ mc_conf_ok mc ∧ mc_init_ok c mc ∧
  installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names
    (heap_regs c.stack_conf.reg_names) mc c'.lab_conf.shmem_extra ms
  ⇒ prune (inr P) F (itree_semantics prog) (machine_sem_itree (mc,ms))
Proof
  rw[] >>
  simp[Q.ISPEC `ARB:((ffi_outcome + word8 list) list) ffi_state` $
        GSYM itree_semantics_itree_of] >>
  irule oracle_IMP_itree_preservation >> simp[extend_with_resource_limit'_def] >>
  reverse conj_tac >- simp[prim_sem_env_eq] >>
  gen_tac >> strip_tac >>
  `(FST $ THE $ prim_sem_env f).eval_state = NONE` by simp[prim_sem_env_eq] >>
  conj_asm1_tac >> gvs[IN_DEF]
  >- (
    simp[itree_semantics, itree_semantics_itree_of] >>
    irule safe_itree_trace_prefix_Error >> simp[] >>
    goal_assum $ drule_at Any >> simp[EVAL ``prim_sem_env f``]
    ) >>
  irule $ SRULE [LET_THM, UNCURRY, start_env] compile_correct >> simp[SF SFY_ss]
QED


(**********)
