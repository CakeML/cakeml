(*
  Relate top-level semantics for function big-step / relational big-step /
  small-step semantics.
*)
open preamble semanticsTheory bigStepTheory smallStepTheory
     semanticPrimitivesPropsTheory bigClockTheory
     smallStepPropsTheory itree_semanticsPropsTheory
     funBigStepEquivTheory bigSmallEquivTheory itree_semanticsEquivTheory

val _ = set_grammar_ancestry ["semantics", "bigStep", "smallStep",
                              "semanticPrimitivesProps", "bigClock",
                              "smallStepProps", "itree_semanticsProps",
                              "funBigStepEquiv", "bigSmallEquiv",
                              "itree_semanticsEquiv"];

val _ = new_theory "alt_semantics";

Theorem big_step_semantics:
  st.eval_state = NONE ⇒ (
  (semantics_prog st env prog (Terminate outcome io_list) ⇔
    ∃st' res ex env'.
      evaluate_decs F env st prog (st', res) ∧
      st'.ffi.io_events = io_list ∧
      if outcome = Success then
        res = Rval env' ∨ res = Rerr (Rraise ex)
      else ∃f. outcome = FFI_outcome f ∧ res = Rerr (Rabort $ Rffi_error f)) ∧
   (semantics_prog st env prog (Diverge io_trace) ⇔
      (∀k. ∃st'.
        evaluate_decs T env (st with clock := k) prog
          (st',Rerr (Rabort Rtimeout_error))) ∧
      lprefix_lub
        { fromList s.ffi.io_events |
            ∃k r. evaluate_decs T env (st with clock := k) prog (s,r) }
        io_trace) ∧
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
    qexists_tac `c` >> simp[] >> every_case_tac >> gvs[]
    )
  >- (
    simp[semantics_prog_def, evaluate_prog_with_clock_def] >>
    simp[GSYM functional_evaluate_decs] >>
    qmatch_goalsub_abbrev_tac `lprefix_lub foo` >>
    qmatch_goalsub_abbrev_tac `_ ⇔ _ ∧ lprefix_lub bar _` >>
    `foo = bar` by (
      unabbrev_all_tac >> rw[EXTENSION, SF DNF_ss] >> eq_tac >> rw[]
      >- ( pairarg_tac >> gvs[] >> metis_tac[])
      >- (qexists_tac `k` >> simp[])) >>
    gvs[] >> eq_tac >> rw[] >>
    last_x_assum $ qspec_then `k` assume_tac >> gvs[] >> pairarg_tac >> gvs[]
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

Theorem small_step_semantics:
  st.eval_state = NONE ⇒ (
  (semantics_prog st env prog (Terminate outcome io_list) ⇔
    ∃st' res ex env'.
      small_eval_decs env st prog (st', res) ∧
      st'.ffi.io_events = io_list ∧
      if outcome = Success then
        res = Rval env' ∨ res = Rerr (Rraise ex)
      else ∃f. outcome = FFI_outcome f ∧ res = Rerr (Rabort $ Rffi_error f)) ∧
  (semantics_prog st env prog (Diverge io_trace) ⇔
    small_decl_diverges env (st, Decl (Dlocal [] prog), []) ∧
    lprefix_lub
      { fromList (FST s).ffi.io_events |
          (decl_step_reln env)꙳ (st, Decl (Dlocal [] prog), []) s }
      io_trace) ∧
  (semantics_prog st env prog Fail ⇔
    ∃st'.
      small_eval_decs env st prog (st', Rerr (Rabort Rtype_error)))
  )
Proof
  rw[big_step_semantics, small_big_decs_equiv] >>
  simp[GSYM small_big_decs_equiv_diverge, GSYM decs_diverges_big_clocked] >>
  Cases_on `decs_diverges env st prog` >> gvs[] >>
  simp[lprefix_lub_big_small]
QED

Theorem itree_semantics:
  st.eval_state = NONE ⇒ (
  (semantics_prog st env prog (Terminate outcome io_list) ⇔
    ∃n io res.
      trace_prefix n (itree_ffi st) (itree_of st env prog) = (io, SOME res) ∧
      io_list = st.ffi.io_events ++ io ∧
      if outcome = Success then res = Termination
      else ∃s conf ws f.
              outcome = FFI_outcome (Final_event s conf ws f) ∧
              res = FinalFFI (s,conf,ws) f) ∧
  (semantics_prog st env prog (Diverge io_trace) ⇔
    (∀n. ∃io. trace_prefix n (itree_ffi st) (itree_of st env prog) = (io, NONE)) ∧
    lprefix_lub
      { fromList (st.ffi.io_events ++ io) | io |
        ∃n res. trace_prefix n (itree_ffi st) (itree_of st env prog) = (io,res) }
      io_trace) ∧
  (semantics_prog st env prog Fail ⇔
    ∃n io. trace_prefix n (itree_ffi st) (itree_of st env prog) = (io, SOME Error))
  )
Proof
  rw[small_step_semantics]
  >- ( (* termination *)
    eq_tac >> rw[] >> Cases_on `outcome` >> gvs[]
    >- (imp_res_tac small_eval_decs_trace_prefix_termination >> simp[SF SFY_ss])
    >- (imp_res_tac small_eval_decs_trace_prefix_termination >> simp[SF SFY_ss])
    >- (
      Cases_on `f` >>
      imp_res_tac small_eval_decs_trace_prefix_ffi_error >> simp[SF SFY_ss]
      )
    >- (drule trace_prefix_small_eval_decs_termination >> rw[SF SFY_ss, SF DNF_ss])
    >- (imp_res_tac trace_prefix_small_eval_decs_ffi_error >> simp[SF SFY_ss])
    )
  >- ( (* divergence *)
    `small_decl_diverges env (st,Decl (Dlocal [] prog),[]) =
     (∀n. ∃io. trace_prefix n (itree_ffi st) (itree_of st env prog) = (io,NONE))` by (
      eq_tac >> rw[]
      >- (
        CCONTR_TAC >> gvs[] >>
        qpat_x_assum `small_decl_diverges _ _` mp_tac >> simp[] >>
        rw[GSYM small_decl_total, small_eval_decs_eq_Dlocal] >>
        Cases_on `trace_prefix n (itree_ffi st) (itree_of st env prog)` >> gvs[] >>
        Cases_on `r` >> gvs[] >> Cases_on `x` >> gvs[]
        >- (imp_res_tac trace_prefix_small_eval_decs_termination >> simp[SF SFY_ss])
        >- (imp_res_tac trace_prefix_small_eval_decs_type_error >> simp[SF SFY_ss])
        >- (
          PairCases_on `p` >>
          imp_res_tac trace_prefix_small_eval_decs_ffi_error >> simp[SF SFY_ss]
          )
        )
      >- (
        CCONTR_TAC >> gvs[GSYM small_decl_total, small_eval_decs_eq_Dlocal] >>
        last_x_assum assume_tac >> last_x_assum mp_tac >> simp[] >>
        PairCases_on `b` >> Cases_on `b1` >> gvs[]
        >- (
          imp_res_tac small_eval_decs_trace_prefix_termination >>
          qexists_tac `n` >> simp[]
          ) >>
        Cases_on `e` >> gvs[]
        >- (
          imp_res_tac small_eval_decs_trace_prefix_termination >>
          qexists_tac `n` >> simp[]
          ) >>
        Cases_on `a` >> gvs[]
        >- (
          imp_res_tac small_eval_decs_trace_prefix_type_error >>
          qexists_tac `n` >> simp[]
          )
        >- (
          gvs[GSYM bigSmallEquivTheory.small_big_decs_equiv] >>
          imp_res_tac bigClockTheory.big_dec_unclocked_no_timeout >> gvs[]
          )
        >- (
          Cases_on `f` >> imp_res_tac small_eval_decs_trace_prefix_ffi_error >>
          qexists_tac `n` >> simp[]
          )
        )
      ) >>
    reverse $ Cases_on `small_decl_diverges env (st,Decl (Dlocal [] prog),[])` >>
    gvs[] >- metis_tac[] >>
    irule lprefix_lub_equiv_chain >> irule_at Any IMP_equiv_lprefix_chain >>
    simp[lprefix_chain_RTC_decl_step_reln, lprefix_chain_trace_prefix] >>
    rw[lprefix_rel_def, PULL_EXISTS, LPREFIX_fromList, from_toList]
    >- (
      PairCases_on `s` >> drule decl_step_trace_prefix_io_events >> rw[] >>
      goal_assum drule >> simp[]
      )
    >- (
      `res = NONE` by (first_x_assum $ qspec_then `n` assume_tac >> gvs[]) >> gvs[] >>
      drule trace_prefix_decl_step_io_events >> rw[] >> goal_assum drule >> simp[]
      )
    )
  >- ( (* type error *)
    eq_tac >> rw[]
    >- (drule small_eval_decs_trace_prefix_type_error >> rw[] >> simp[SF SFY_ss])
    >- (drule trace_prefix_small_eval_decs_type_error >> rw[SF SFY_ss])
    )
QED


val _ = export_theory();
