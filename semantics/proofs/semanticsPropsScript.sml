open preamble
     evaluateTheory
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
  metis_tac[LESS_EQ_CASES,evaluate_decs_ffi_mono_clock,io_events_mono_def,FST]);

val semantics_prog_total = Q.store_thm("semantics_prog_total",
  `∀s e p. ∃b. semantics_prog s e p b`,
  srw_tac[][] >>
  Cases_on`∃k. SND(evaluate_prog_with_clock s e k p) = Rerr (Rabort Rtype_error)`
  >- metis_tac[semantics_prog_def] >> full_simp_tac(srw_ss())[] >>
  Cases_on`∃k ffi r.
    evaluate_prog_with_clock s e k p = (ffi,r) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    (ffi.final_event = NONE ⇒ r ≠ Rerr (Rabort Rtimeout_error))`
  >- metis_tac[semantics_prog_def,SND] >> full_simp_tac(srw_ss())[] >>
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

val with_clock_ffi = Q.prove(
  `(s with clock := x).ffi = s.ffi`,EVAL_TAC)

val tac1 =
    metis_tac[semanticPrimitivesTheory.result_11,evaluate_decs_ffi_mono_clock,io_events_mono_def,
              semanticPrimitivesTheory.error_result_11,option_nchotomy,LESS_EQ_CASES,
              semanticPrimitivesTheory.abort_distinct,pair_CASES,FST,THE_DEF,
              PAIR_EQ,IS_SOME_EXISTS,SOME_11,NOT_SOME_NONE,SND,PAIR,LESS_OR_EQ]

val semantics_prog_deterministic = Q.store_thm("semantics_prog_deterministic",
  `∀s e p b b'.
    semantics_prog s e p b ∧
    semantics_prog s e p b' ⇒
    b = b'`,
  rw []
  >> Cases_on `b`
  >> Cases_on `b'`
  >> fs [semantics_prog_def]
  >- metis_tac[unique_lprefix_lub]
  >- tac1
  >- tac1
  >- tac1
  >- (
    fs [evaluate_prog_with_clock_def]
    >> pairarg_tac
    >> fs []
    >> pairarg_tac
    >> fs []
    >> rpt var_eq_tac
    >> pop_assum mp_tac
    >> drule evaluate_decs_clock_determ
    >> ntac 2 DISCH_TAC
    >> first_x_assum drule
    >> simp []
    >> every_case_tac
    >> fs [semanticPrimitivesTheory.state_component_equality]
    >> tac1)
  >- tac1
  >- tac1
  >- tac1);

val semantics_prog_Terminate_not_Fail = Q.store_thm("semantics_prog_Terminate_not_Fail",
  `semantics_prog s e p (Terminate x y) ⇒
    ¬semantics_prog s e p Fail ∧
    semantics_prog s e p = {Terminate x y}`,
  rpt strip_tac
  \\ simp[FUN_EQ_THM]
  \\ imp_res_tac semantics_prog_deterministic \\ fs[]
  \\ metis_tac[semantics_prog_deterministic]);

val state_invariant_def = Define`
  state_invariant st ⇔
  ?ctMap tenvS.
    FRANGE ((SND ∘ SND) o_f ctMap) ⊆ st.type_ids ∧
    type_sound_invariant st.sem_st st.sem_env ctMap tenvS {} st.tenv`;

val clock_lemmas = Q.prove(
  `((x with clock := c).clock = c) ∧
   (((x with clock := c) with clock := d) = (x with clock := d)) ∧
   (x with clock := x.clock = x)`,
  srw_tac[][semanticPrimitivesTheory.state_component_equality])

val semantics_deterministic = Q.store_thm("semantics_deterministic",
  `state_invariant st ⇒
   semantics st prelude inp = Execute bs
   ⇒ ∃b. bs = {b} ∧ b ≠ Fail`,
 rw [state_invariant_def, semantics_def]
 >> every_case_tac
 >> fs [can_type_prog_def]
 >> rw []
 >> qspecl_then [`st.sem_st`, `st.sem_env`, `prelude ++ x`] strip_assume_tac semantics_prog_total
 >> imp_res_tac semantics_type_sound
 >> qexists_tac `b`
 >> rw [EXTENSION, IN_DEF]
 >- metis_tac [semantics_prog_deterministic] >>
 `DISJOINT new_tids (FRANGE ((SND ∘ SND) o_f ctMap))`
 by (
   fs [DISJOINT_DEF, EXTENSION, SUBSET_DEF] >>
   rw [] >>
   metis_tac []) >>
 fs [typeSoundInvariantsTheory.type_sound_invariant_def] >>
 rfs [typeSoundInvariantsTheory.consistent_ctMap_def] >>
 metis_tac []);

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

val implements_intro = Q.store_thm("implements_intro",
  `(b /\ x <> Fail ==> y = x) ==> b ==> implements {y} {x}`,
  full_simp_tac(srw_ss())[implements_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[extend_with_resource_limit_def]);

val implements_trivial_intro = Q.store_thm("implements_trivial_intro",
  `(y = x) ==> implements {y} {x}`,
  full_simp_tac(srw_ss())[implements_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[extend_with_resource_limit_def]);

val implements_intro_ext = Q.store_thm("implements_intro_ext",
  `(b /\ x <> Fail ==> y IN extend_with_resource_limit {x}) ==>
    b ==> implements {y} {x}`,
  full_simp_tac(srw_ss())[implements_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[extend_with_resource_limit_def]);

val isPREFIX_IMP_LPREFIX = Q.prove(
  `!xs ys. isPREFIX xs ys ==> LPREFIX (fromList xs) (fromList ys)`,
  full_simp_tac(srw_ss())[LPREFIX_def,llistTheory.from_toList]);

val implements_trans = Q.store_thm("implements_trans",
  `implements y z ==> implements x y ==> implements x z`,
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
