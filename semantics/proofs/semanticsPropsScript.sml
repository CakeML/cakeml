open preamble
     evaluatePropsTheory
     semanticsTheory lprefix_lubTheory
     typeSoundTheory;

val _ = new_theory"semanticsProps"

val evaluate_prog_io_events_chain = Q.store_thm("evaluate_prog_io_events_chain",
  `lprefix_chain (IMAGE (λk. fromList (FST (evaluate_prog_with_clock st env k prog)).io_events) UNIV)`,
  qho_match_abbrev_tac`lprefix_chain (IMAGE (λk. fromList (g k)) UNIV)` >>
  ONCE_REWRITE_TAC[GSYM o_DEF] >>
  REWRITE_TAC[IMAGE_COMPOSE] >>
  match_mp_tac prefix_chain_lprefix_chain >>
  srw_tac[][prefix_chain_def,Abbr`g`,evaluate_prog_with_clock_def] >> srw_tac[][] >>
  metis_tac[LESS_EQ_CASES,evaluate_prog_ffi_mono_clock,FST]);

val semantics_prog_total = Q.store_thm("semantics_prog_total",
  `∀s e p. ∃b. semantics_prog s e p b`,
  srw_tac[][] >>
  Cases_on`∃k. SND(evaluate_prog_with_clock s e k p) = Rerr (Rabort Rtype_error)`
  >- metis_tac[semantics_prog_def] >> full_simp_tac(srw_ss())[] >>
  Cases_on`∃k ffi r.
    evaluate_prog_with_clock s e k p = (ffi,r) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    (ffi.final_event = NONE ⇒ ∀a. r ≠ Rerr (Rabort a))`
  >- metis_tac[semantics_prog_def] >> full_simp_tac(srw_ss())[] >>
  qexists_tac`Diverge (build_lprefix_lub (IMAGE (λk. fromList (FST (evaluate_prog_with_clock s e k p)).io_events) UNIV))` >>
  simp[semantics_prog_def] >>
  conj_tac >- (
    strip_tac >>
    rpt(first_x_assum(qspec_then`k`mp_tac)) >>
    Cases_on`evaluate_prog_with_clock s e k p`>>simp[]>>
    Cases_on`r`>>simp[]>>
    Cases_on`e'`>>simp[]>>
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
  impl_tac >- (simp[] >> metis_tac[]) >>
  qspecl_then[`x`,`y`,`z`,`t with clock := y.clock`,`u`](mp_tac o #2 o EQ_IMP_RULE)(prog_clocked_unclocked_equiv) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  metis_tac[prog_determ,PAIR_EQ])

val prog_clocked_timeout_smaller = Q.prove(
  `evaluate_prog T x (y with clock := a) z (p,q,r) ∧
   evaluate_prog T x (y with clock := b) z (t,u,Rerr (Rabort Rtimeout_error)) ∧
   r ≠ Rerr (Rabort	Rtimeout_error)
   ⇒
   b < a`,
  rpt strip_tac >>
  CCONTR_TAC >> full_simp_tac(srw_ss())[NOT_LESS] >>
  full_simp_tac(srw_ss())[LESS_EQ_EXISTS] >>
  imp_res_tac prog_add_to_counter >> rev_full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  metis_tac[prog_determ,PAIR_EQ])

val with_clock_ffi = Q.prove(
  `(s with clock := x).ffi = s.ffi`,EVAL_TAC)

val tac0 =
    full_simp_tac(srw_ss())[evaluate_prog_with_clock_def,LET_THM] >>
    first_assum(split_uncurry_arg_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >>
    first_assum(split_uncurry_arg_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >>
    imp_res_tac functional_evaluate_prog >>
    full_simp_tac(srw_ss())[bigStepTheory.evaluate_whole_prog_def]

val tac1 =
    metis_tac[semanticPrimitivesTheory.result_11,
              semanticPrimitivesTheory.error_result_11,
              semanticPrimitivesTheory.abort_distinct,
              PAIR_EQ,IS_SOME_EXISTS,NOT_SOME_NONE,SND,PAIR]

val semantics_prog_deterministic = Q.store_thm("semantics_prog_deterministic",
  `∀s e p b b'.
    semantics_prog s e p b ∧ b ≠ Fail ∧
    semantics_prog s e p b' ∧ b' ≠ Fail ⇒
    b = b'`,
  ntac 3 gen_tac >> reverse Cases >> srw_tac[][semantics_prog_def]
  >- (
    Cases_on`b'`>>full_simp_tac(srw_ss())[semantics_prog_def]
    >- tac1
    >- (
      tac0 >>
      qmatch_assum_abbrev_tac`if X then Y else Z` >>
      reverse(Cases_on`X`)>>full_simp_tac(srw_ss())[Abbr`Y`,Abbr`Z`] >- (
        rpt var_eq_tac >> full_simp_tac(srw_ss())[] ) >>
      Cases_on`∃a a'. r = Rerr (Rabort a) ∧ r' = Rerr (Rabort a')` >> full_simp_tac(srw_ss())[] >- (
        metis_tac[LESS_EQ_CASES,
                  evaluate_prog_ffi_mono_clock,
                  FST,THE_DEF,IS_SOME_EXISTS,NOT_SOME_NONE,option_CASES] ) >>
      Cases_on`r = Rerr (Rabort Rtimeout_error) ∨ r' = Rerr (Rabort Rtimeout_error)` >- (
        metis_tac[prog_clocked_timeout_smaller,
                  LESS_IMP_LESS_OR_EQ,
                  evaluate_prog_ffi_mono_clock,
                  FST,THE_DEF,IS_SOME_EXISTS,NOT_SOME_NONE,option_CASES] ) >>
      imp_res_tac prog_clocked_min_counter >> full_simp_tac(srw_ss())[] >>
      first_x_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO](GEN_ALL prog_clocked_zero_determ))) >>
      disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
      simp[semanticPrimitivesTheory.state_component_equality] >>
      srw_tac[][] >> every_case_tac >> rev_full_simp_tac(srw_ss())[]))
  >- (
    Cases_on`b'`>>full_simp_tac(srw_ss())[semantics_prog_def]
    >- metis_tac[unique_lprefix_lub] >>
    tac1))

    (*
val state_invariant_def = Define`
  state_invariant st ⇔
  type_sound_invariants (NONE:(v,v)result option) (st.tdecs,st.tenv,st.sem_st,st.sem_env)`;
  *)

val clock_lemmas = Q.prove(
  `((x with clock := c).clock = c) ∧
   (((x with clock := c) with clock := d) = (x with clock := d)) ∧
   (x with clock := x.clock = x)`,
  srw_tac[][semanticPrimitivesTheory.state_component_equality])

val prog_diverges_semantics_prog = Q.store_thm("prog_diverges_semantics_prog",
  `prog_diverges st.sem_env st.sem_st prog ∧
   no_dup_mods prog st.sem_st.defined_mods ∧
   no_dup_top_types prog st.sem_st.defined_types ⇒
   ¬semantics_prog st.sem_st st.sem_env prog Fail`,
  strip_tac >>
  (untyped_safety_prog
   |> SPEC_ALL
   |> EQ_IMP_RULE |> fst
   |> CONTRAPOS
   |> SIMP_RULE bool_ss []
   |> imp_res_tac) >>
  simp[semantics_prog_def,PULL_EXISTS] >>
  srw_tac[][evaluate_prog_with_clock_def] >>
  imp_res_tac functional_evaluate_prog >>
  rev_full_simp_tac(srw_ss())[bigStepTheory.evaluate_whole_prog_def] >>
  full_simp_tac(srw_ss())[prog_clocked_unclocked_equiv,FORALL_PROD] >>
  imp_res_tac prog_clocked_min_counter >> full_simp_tac(srw_ss())[] >>
  spose_not_then strip_assume_tac >>
  Cases_on`envC`>>full_simp_tac(srw_ss())[] >>
  metis_tac[clock_lemmas,
            semanticPrimitivesTheory.result_11,
            semanticPrimitivesTheory.error_result_11,
            semanticPrimitivesTheory.abort_distinct])

            (*
val semantics_deterministic = Q.store_thm("semantics_deterministic",
  `state_invariant st ⇒
   semantics st prelude inp = Execute bs
   ⇒ ∃b. bs = {b} ∧ b ≠ Fail`,
  srw_tac[][semantics_def] >> every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  `∀b. semantics_prog st.sem_st st.sem_env (prelude ++ x) b ⇒ b ≠ Fail` by(
    full_simp_tac(srw_ss())[can_type_prog_def,state_invariant_def] >>
    Cases_on`prog_diverges st.sem_env st.sem_st (prelude ++ x)` >- (
      imp_res_tac prog_diverges_semantics_prog >> metis_tac[] ) >>
    full_simp_tac(srw_ss())[semantics_prog_def,evaluate_prog_with_clock_def,LET_THM] >>
    CCONTR_TAC >> full_simp_tac(srw_ss())[] >>
    first_assum(split_uncurry_arg_tac o rand o lhs o concl) >>
    imp_res_tac functional_evaluate_prog >>
    (whole_prog_type_soundness
     |> REWRITE_RULE[GSYM AND_IMP_INTRO]
     |> (fn th => first_x_assum(mp_tac o MATCH_MP th))) >>
    PairCases_on`new_tenv`>>
    disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    simp[PULL_EXISTS] >> full_simp_tac(srw_ss())[] >>
    rev_full_simp_tac(srw_ss())[bigStepTheory.evaluate_whole_prog_def] >>
    simp[prog_clocked_unclocked_equiv,PULL_EXISTS] >>
    CCONTR_TAC >> full_simp_tac(srw_ss())[] >>
    imp_res_tac prog_clocked_min_counter >> full_simp_tac(srw_ss())[] >>
    metis_tac[prog_clocked_zero_determ,SND,PAIR_EQ,
              semanticPrimitivesTheory.result_11,
              semanticPrimitivesTheory.result_distinct,
              semanticPrimitivesTheory.error_result_11,
              semanticPrimitivesTheory.abort_distinct]) >>
  simp[FUN_EQ_THM] >>
  metis_tac[semantics_prog_total,semantics_prog_deterministic])
  *)

val extend_with_resource_limit_def = Define`
  extend_with_resource_limit behaviours =
  behaviours ∪
  { Terminate Resource_limit_hit io_list
    | io_list | ∃t l. Terminate t l ∈ behaviours ∧ io_list ≼ l } ∪
  { Terminate Resource_limit_hit io_list
    | io_list | ∃ll. Diverge ll ∈ behaviours ∧ LPREFIX (fromList io_list) ll }`;

val implements_def = Define `
  implements x y <=>
    (~(Fail IN y) ==> x SUBSET extend_with_resource_limit y)`;

val implements_intro = store_thm("implements_intro",
  ``(b /\ x <> Fail ==> y = x) ==> b ==> implements {y} {x}``,
  full_simp_tac(srw_ss())[implements_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[extend_with_resource_limit_def]);

val implements_trivial_intro = store_thm("implements_trivial_intro",
  ``(y = x) ==> implements {y} {x}``,
  full_simp_tac(srw_ss())[implements_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[extend_with_resource_limit_def]);

val implements_intro_ext = store_thm("implements_intro_ext",
  ``(b /\ x <> Fail ==> y IN extend_with_resource_limit {x}) ==>
    b ==> implements {y} {x}``,
  full_simp_tac(srw_ss())[implements_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[extend_with_resource_limit_def]);

val isPREFIX_IMP_LPREFIX = prove(
  ``!xs ys. isPREFIX xs ys ==> LPREFIX (fromList xs) (fromList ys)``,
  full_simp_tac(srw_ss())[LPREFIX_def,llistTheory.from_toList]);

val implements_trans = store_thm("implements_trans",
  ``implements y z ==> implements x y ==> implements x z``,
  full_simp_tac(srw_ss())[implements_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[extend_with_resource_limit_def]
  \\ Cases_on `Fail IN y` \\ full_simp_tac(srw_ss())[]
  THEN1 (full_simp_tac(srw_ss())[SUBSET_DEF] \\ res_tac \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[SUBSET_DEF] \\ srw_tac[][] \\ rename1 `a IN x`
  \\ reverse (res_tac \\ full_simp_tac(srw_ss())[])
  THEN1 (res_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ metis_tac [])
  \\ res_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ imp_res_tac IS_PREFIX_TRANS
  \\ imp_res_tac isPREFIX_IMP_LPREFIX
  \\ imp_res_tac LPREFIX_TRANS
  \\ metis_tac [])

val _ = export_theory()
