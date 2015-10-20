open preamble
     determTheory
     funBigStepEquivTheory
     bigClockTheory
     semanticsTheory
     lprefix_lubTheory

val _ = new_theory"semanticsProps"

(* TODO: move *)
val evaluate_prog_io_events_mono = Q.store_thm("evaluate_prog_io_events_mono",
  `∀k1 k2 s e p.
    k1 ≤ k2 ⇒
    (FST (evaluate_prog (s with clock := k1) e p)).ffi.io_events ≼
    (FST (evaluate_prog (s with clock := k2) e p)).ffi.io_events`,
  cheat)
(* -- *)

val semantics_prog_total = Q.store_thm("semantics_prog_total",
  `∀s p. ∃b. semantics_prog s p b`,
  rw[] >>
  Cases_on`∃k ffi. evaluate_prog_with_clock s k p = (ffi,Rerr (Rabort Rtype_error))`
  >- metis_tac[semantics_prog_def] >> fs[] >>
  Cases_on`∃k ffi r.
    evaluate_prog_with_clock s k p = (ffi,r) ∧
    (r = Rerr (Rabort Rtimeout_error) ⇒ IS_SOME ffi.final_event)`
  >- metis_tac[semantics_prog_def] >> fs[] >>
  qexists_tac`Diverge (build_lprefix_lub (IMAGE (λk. fromList (FST (evaluate_prog_with_clock s k p)).io_events) UNIV))` >>
  simp[semantics_prog_def] >>
  conj_tac >- metis_tac[PAIR] >>
  match_mp_tac build_lprefix_lub_thm >>
  qho_match_abbrev_tac`lprefix_chain (IMAGE (λk. fromList (g k)) UNIV)` >>
  ONCE_REWRITE_TAC[GSYM o_DEF] >>
  REWRITE_TAC[IMAGE_COMPOSE] >>
  match_mp_tac prefix_chain_lprefix_chain >>
  rw[prefix_chain_def,Abbr`g`,evaluate_prog_with_clock_def] >> rw[] >>
  metis_tac[LESS_EQ_CASES,evaluate_prog_io_events_mono,FST]);

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

(*
val semantics_prog_deterministic = Q.store_thm("semantics_prog_deterministic",
  `∀s p b b'. semantics_prog s p b ∧
              semantics_prog s p b' ⇒
              b = b'`,
  ntac 2 gen_tac >> reverse Cases >> rw[semantics_prog_def] >- (
    Cases_on`b'`>>fs[semantics_prog_def] >-
      metis_tac[semanticPrimitivesTheory.result_11,
                semanticPrimitivesTheory.error_result_11,
                semanticPrimitivesTheory.abort_distinct,
                PAIR_EQ] >>
    fs[evaluate_prog_with_clock_def,LET_THM] >>
    first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >> rw[] >>
    first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >> rw[] >>
    imp_res_tac functional_evaluate_prog >>
    fs[bigStepTheory.evaluate_whole_prog_def] >>
    every_case_tac >> fs[] >>
    imp_res_tac prog_clocked_min_counter >> fs[] >>
    imp_res_tac prog_clocked_zero_determ >> rfs[] )
  >- (
    Cases_on`b'`>>fs[semantics_prog_def]
    >- metis_tac[semanticPrimitivesTheory.result_11,
                 semanticPrimitivesTheory.error_result_11,
                 semanticPrimitivesTheory.abort_distinct,
                 PAIR_EQ]
    >- (
      fs[evaluate_prog_with_clock_def,LET_THM] >>
      first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >> rpt var_eq_tac >>
      first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >> rpt var_eq_tac >>
      imp_res_tac functional_evaluate_prog >>
      fs[bigStepTheory.evaluate_whole_prog_def] >>
      pop_assum mp_tac >> IF_CASES_TAC >> fs[] >> strip_tac >>
      imp_res_tac prog_clocked_min_counter >> fs[] >>
      imp_res_tac prog_clocked_zero_determ >>
      rfs[semanticPrimitivesTheory.state_component_equality] )
    >- (
      fs[evaluate_prog_with_clock_def,LET_THM] >>
      first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >> rpt var_eq_tac >>
      first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >> rpt var_eq_tac >>
      imp_res_tac functional_evaluate_prog >>
      fs[bigStepTheory.evaluate_whole_prog_def] >>
      every_case_tac >> fs[] >>
      imp_res_tac prog_clocked_min_counter >> fs[] >>
      imp_res_tac prog_clocked_zero_determ >> rfs[] ))
  >- (
    Cases_on`b'`>>fs[semantics_prog_def]
    >- metis_tac[unique_lprefix_lub] >>
    metis_tac[semanticPrimitivesTheory.result_11,
              semanticPrimitivesTheory.error_result_11,
              semanticPrimitivesTheory.abort_distinct,
              PAIR_EQ]))
*)

val _ = export_theory()
