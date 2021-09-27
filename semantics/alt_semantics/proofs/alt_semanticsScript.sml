(*
  Relate top-level semantics for function big-step / relational big-step /
  small-step semantics.
*)
open preamble semanticsTheory bigStepTheory smallStepTheory
     semanticPrimitivesPropsTheory bigClockTheory
     funBigStepEquivTheory bigSmallEquivTheory

val _ = new_theory "alt_semantics";

Triviality choice_big_step:
  ∀st k env prog res.
  st.eval_state = NONE ⇒
  (@res. evaluate_decs T env (st with clock := k) prog res) =
  evaluate_decs (st with clock := k) env prog
Proof
  rw[] >> DEEP_INTRO_TAC SELECT_ELIM_THM >> rw[]
  >- simp[interpTheory.evaluate_decs_run_eval_decs] >>
  PairCases_on `x` >> gvs[functional_evaluate_decs]
QED

Theorem big_step_semantics:
  st.eval_state = NONE ⇒ (
  (semantics_prog st env prog (Terminate Success io_list) ⇔
    ∃st' res ex env'.
      evaluate_decs F env st prog (st', res) ∧
      (res = Rval env' ∨ res = Rerr (Rraise ex)) ∧
      st'.ffi.io_events = io_list) ∧
  ((semantics_prog st env prog (Diverge io_trace)) ⇔
      (∀k. ∃st'.
        evaluate_decs T env (st with clock := k) prog
          (st',Rerr (Rabort Rtimeout_error))) ∧
      lprefix_lub
        (IMAGE (λk. fromList
          (FST (@res. evaluate_decs T env (st with clock := k) prog res)).ffi.io_events)
          UNIV) io_trace) ∧
  (semantics_prog st env prog Fail ⇔
    ∃st'.
      evaluate_decs F env st prog (st', Rerr (Rabort Rtype_error)))
  )
Proof
  strip_tac >> rpt conj_tac
  >- (
    rw[semantics_prog_def] >> eq_tac >> rw[] >> gvs[]
    >- (
      every_case_tac >> gvs[] >>
      gvs[evaluate_prog_with_clock_def] >> pairarg_tac >> gvs[] >>
      drule_at (Pos last) $ iffLR functional_evaluate_decs >> rw[] >>
      drule $ cj 2 evaluate_decs_clocked_to_unclocked >> simp[] >>
      disch_then $ qspec_then `st.clock` mp_tac >> rw[with_same_clock] >>
      goal_assum drule >> simp[]
      ) >>
    simp[evaluate_prog_with_clock_def] >>
    drule $ cj 2 evaluate_decs_unclocked_to_clocked >>
    simp[GSYM functional_evaluate_decs] >> strip_tac >> gvs[] >>
    qexists_tac `c` >> simp[]
    )
  >- (
    simp[choice_big_step] >>
    simp[semantics_prog_def, evaluate_prog_with_clock_def] >>
    simp[GSYM functional_evaluate_decs] >> eq_tac >> rw[] >> gvs[]
    >- (
      last_x_assum $ qspec_then `k` assume_tac >> gvs[] >>
      pairarg_tac >> gvs[]
      )
    >- gvs[UNCURRY]
    >- (last_x_assum $ qspec_then `k` assume_tac >> gvs[])
    >- gvs[UNCURRY]
    )
  >- (
    rw[semantics_prog_def] >> eq_tac >> rw[] >>
    gvs[evaluate_prog_with_clock_def]
    >- (
      pairarg_tac >> gvs[] >>
      drule_at (Pos last) $ iffLR functional_evaluate_decs >> rw[] >>
      drule $ cj 2 evaluate_decs_clocked_to_unclocked >> simp[] >>
      disch_then $ qspec_then `st.clock` mp_tac >> rw[with_same_clock] >>
      goal_assum drule >> simp[]
      ) >>
    simp[evaluate_prog_with_clock_def] >>
    drule $ cj 2 evaluate_decs_unclocked_to_clocked >>
    simp[GSYM functional_evaluate_decs] >> strip_tac >> gvs[] >>
    qexists_tac `c` >> simp[]
    )
QED

val _ = export_theory();
