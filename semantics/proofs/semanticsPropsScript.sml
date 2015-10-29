open preamble
     funBigStepEquivTheory funBigStepPropsTheory
     determTheory bigClockTheory
     semanticsTheory lprefix_lubTheory
     typeSoundTheory untypedSafetyTheory

val _ = new_theory"semanticsProps"

val evaluate_prog_io_events_chain = Q.store_thm("evaluate_prog_io_events_chain",
  `lprefix_chain (IMAGE (λk. fromList (FST (evaluate_prog_with_clock st k prog)).io_events) UNIV)`,
  qho_match_abbrev_tac`lprefix_chain (IMAGE (λk. fromList (g k)) UNIV)` >>
  ONCE_REWRITE_TAC[GSYM o_DEF] >>
  REWRITE_TAC[IMAGE_COMPOSE] >>
  match_mp_tac prefix_chain_lprefix_chain >>
  rw[prefix_chain_def,Abbr`g`,evaluate_prog_with_clock_def] >> rw[] >>
  metis_tac[LESS_EQ_CASES,evaluate_prog_ffi_mono_clock,FST]);

val semantics_prog_total = Q.store_thm("semantics_prog_total",
  `∀s p. ∃b. semantics_prog s p b`,
  rw[] >>
  Cases_on`∃k. SND(evaluate_prog_with_clock s k p) = Rerr (Rabort Rtype_error)`
  >- metis_tac[semantics_prog_def] >> fs[] >>
  Cases_on`∃k ffi r.
    evaluate_prog_with_clock s k p = (ffi,r) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    (ffi.final_event = NONE ⇒ ∀a. r ≠ Rerr (Rabort a))`
  >- metis_tac[semantics_prog_def] >> fs[] >>
  qexists_tac`Diverge (build_lprefix_lub (IMAGE (λk. fromList (FST (evaluate_prog_with_clock s k p)).io_events) UNIV))` >>
  simp[semantics_prog_def] >>
  conj_tac >- (
    strip_tac >>
    rpt(first_x_assum(qspec_then`k`mp_tac)) >>
    Cases_on`evaluate_prog_with_clock s k p`>>simp[]>>
    Cases_on`r`>>simp[]>>
    Cases_on`e`>>simp[]>>
    Cases_on`a`>>simp[]) >>
  match_mp_tac build_lprefix_lub_thm >>
  MATCH_ACCEPT_TAC evaluate_prog_io_events_chain);

val prog_clocked_zero_determ = Q.prove(
  `evaluate_prog T x (y with clock := a) z (s with clock := 0,r) ∧
   evaluate_prog T x (y with clock := b) z (t with clock := 0,u) ∧
   SND r ≠ Rerr (Rabort Rtimeout_error) ∧
   SND u ≠ Rerr (Rabort Rtimeout_error) ⇒
   r = u ∧ (s with clock := y.clock) = (t with clock := y.clock)`,
  strip_tac >>
  qspecl_then[`x`,`y`,`z`,`s with clock := y.clock`,`r`](mp_tac o #2 o EQ_IMP_RULE)(prog_clocked_unclocked_equiv) >>
  discharge_hyps >- (simp[] >> metis_tac[]) >>
  qspecl_then[`x`,`y`,`z`,`t with clock := y.clock`,`u`](mp_tac o #2 o EQ_IMP_RULE)(prog_clocked_unclocked_equiv) >>
  discharge_hyps >- (simp[] >> metis_tac[]) >>
  metis_tac[prog_determ,PAIR_EQ])

val prog_clocked_timeout_smaller = Q.prove(
  `evaluate_prog T x (y with clock := a) z (p,q,r) ∧
   evaluate_prog T x (y with clock := b) z (t,u,Rerr (Rabort Rtimeout_error)) ∧
   r ≠ Rerr (Rabort	Rtimeout_error)
   ⇒
   b < a`,
  rpt strip_tac >>
  CCONTR_TAC >> fs[NOT_LESS] >>
  fs[LESS_EQ_EXISTS] >>
  imp_res_tac prog_add_to_counter >> rfs[] >>
  rw[] >>
  metis_tac[prog_determ,PAIR_EQ])

val with_clock_ffi = Q.prove(
  `(s with clock := x).ffi = s.ffi`,EVAL_TAC)

val tac0 =
    fs[evaluate_prog_with_clock_def,LET_THM] >>
    first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >> rpt var_eq_tac >>
    first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >> rpt var_eq_tac >>
    imp_res_tac functional_evaluate_prog >>
    fs[bigStepTheory.evaluate_whole_prog_def]

val tac1 =
    metis_tac[semanticPrimitivesTheory.result_11,
              semanticPrimitivesTheory.error_result_11,
              semanticPrimitivesTheory.abort_distinct,
              PAIR_EQ,IS_SOME_EXISTS,NOT_SOME_NONE,SND,PAIR]

val semantics_prog_deterministic = Q.store_thm("semantics_prog_deterministic",
  `∀s p b b'.
    semantics_prog s p b ∧ b ≠ Fail ∧
    semantics_prog s p b' ∧ b' ≠ Fail ⇒
    b = b'`,
  ntac 2 gen_tac >> reverse Cases >> rw[semantics_prog_def]
  >- (
    Cases_on`b'`>>fs[semantics_prog_def]
    >- tac1
    >- (
      tac0 >>
      qmatch_assum_abbrev_tac`if X then Y else Z` >>
      reverse(Cases_on`X`)>>fs[Abbr`Y`,Abbr`Z`] >- (
        rpt var_eq_tac >> fs[] ) >>
      Cases_on`∃a a'. r = Rerr (Rabort a) ∧ r' = Rerr (Rabort a')` >> fs[] >- (
        metis_tac[LESS_EQ_CASES,
                  evaluate_prog_ffi_mono_clock,
                  FST,THE_DEF,IS_SOME_EXISTS,NOT_SOME_NONE,option_CASES] ) >>
      Cases_on`r = Rerr (Rabort Rtimeout_error) ∨ r' = Rerr (Rabort Rtimeout_error)` >- (
        metis_tac[prog_clocked_timeout_smaller,
                  LESS_IMP_LESS_OR_EQ,
                  evaluate_prog_ffi_mono_clock,
                  FST,THE_DEF,IS_SOME_EXISTS,NOT_SOME_NONE,option_CASES] ) >>
      imp_res_tac prog_clocked_min_counter >> fs[] >>
      first_x_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO](GEN_ALL prog_clocked_zero_determ))) >>
      disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
      simp[semanticPrimitivesTheory.state_component_equality] >>
      rw[] >> every_case_tac >> rfs[]))
  >- (
    Cases_on`b'`>>fs[semantics_prog_def]
    >- metis_tac[unique_lprefix_lub] >>
    tac1))

val state_invariant_def = Define`
  state_invariant st ⇔
  type_sound_invariants (NONE:(v,v)result option) (st.tdecs,st.tenvT,st.tenvM,st.tenvC,st.tenv,st.sem_st,st.sem_env)`;

val clock_lemmas = Q.prove(
  `((x with clock := c).clock = c) ∧
   (((x with clock := c) with clock := d) = (x with clock := d)) ∧
   (x with clock := x.clock = x)`,
  rw[semanticPrimitivesTheory.state_component_equality])

val prog_diverges_semantics_prog = Q.prove(
  `prog_diverges st.sem_env st.sem_st prog ∧
   no_dup_mods prog st.sem_st.defined_mods ∧
   no_dup_top_types prog st.sem_st.defined_types ⇒
   ¬semantics_prog st prog Fail`,
  strip_tac >>
  (untyped_safety_prog
   |> SPEC_ALL
   |> EQ_IMP_RULE |> fst
   |> CONTRAPOS
   |> SIMP_RULE bool_ss []
   |> imp_res_tac) >>
  simp[semantics_prog_def,PULL_EXISTS] >>
  rw[evaluate_prog_with_clock_def] >>
  imp_res_tac functional_evaluate_prog >>
  rfs[bigStepTheory.evaluate_whole_prog_def] >>
  fs[prog_clocked_unclocked_equiv,FORALL_PROD] >>
  imp_res_tac prog_clocked_min_counter >> fs[] >>
  spose_not_then strip_assume_tac >>
  Cases_on`envC`>>fs[] >>
  metis_tac[clock_lemmas,
            semanticPrimitivesTheory.result_11,
            semanticPrimitivesTheory.error_result_11,
            semanticPrimitivesTheory.abort_distinct])

val semantics_deterministic = Q.store_thm("semantics_deterministic",
  `state_invariant st ⇒
   semantics st prelude inp = Execute bs
   ⇒ ∃b. bs = {b} ∧ b ≠ Fail`,
  rw[semantics_def] >> every_case_tac >> fs[] >> rw[] >>
  `∀b. semantics_prog st (prelude ++ x) b ⇒ b ≠ Fail` by(
    fs[can_type_prog_def,state_invariant_def] >>
    Cases_on`prog_diverges st.sem_env st.sem_st (prelude ++ x)` >- (
      imp_res_tac prog_diverges_semantics_prog >> metis_tac[] ) >>
    fs[semantics_prog_def,evaluate_prog_with_clock_def,LET_THM] >>
    CCONTR_TAC >> fs[] >>
    first_assum(split_applied_pair_tac o rand o lhs o concl) >>
    imp_res_tac functional_evaluate_prog >>
    (whole_prog_type_soundness
     |> REWRITE_RULE[GSYM AND_IMP_INTRO]
     |> (fn th => first_x_assum(mp_tac o MATCH_MP th))) >>
    disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    simp[PULL_EXISTS] >> fs[] >>
    rfs[bigStepTheory.evaluate_whole_prog_def] >>
    simp[prog_clocked_unclocked_equiv,PULL_EXISTS] >>
    CCONTR_TAC >> fs[] >>
    imp_res_tac prog_clocked_min_counter >> fs[] >>
    metis_tac[prog_clocked_zero_determ,SND,PAIR_EQ,
              semanticPrimitivesTheory.result_11,
              semanticPrimitivesTheory.result_distinct,
              semanticPrimitivesTheory.error_result_11,
              semanticPrimitivesTheory.abort_distinct]) >>
  simp[FUN_EQ_THM] >>
  metis_tac[semantics_prog_total,semantics_prog_deterministic])

val _ = export_theory()
