open preamble
     determTheory
     funBigStepEquivTheory
     bigClockTheory
     semanticsTheory
     lprefix_lubTheory

val _ = new_theory"semanticsProps"

(*
val semantics_prog_total = Q.store_thm("semantics_prog_total",
  `∀s p. ∃b. semantics_prog s p b`,
*)

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

val _ = export_theory()
