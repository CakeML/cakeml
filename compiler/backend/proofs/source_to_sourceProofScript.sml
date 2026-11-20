(*
  Proof of correctness for source_to_source. The proofs are about
  evalSem in EvalDecs mode.
 *)
Theory source_to_sourceProof
Ancestors
  source_letProof source_dceProof source_lift_constsProof
  source_adjust_decsProof source_to_source evalSem evalSemProps
Libs
  preamble

Theorem compile_decs_semantics:
  env.v = nsEmpty ∧
  (∀x. s.eval_state = SOME x ⇒ ∃ev. x = EvalDecs ev) ∧
  ¬semantics_determ s env prog Fail ∧
  semantics_determ s env prog outcome ⇒
    semantics_determ s env
      (source_lift_consts$compile_decs
        (source_let$compile_decs (source_dce$compile_decs prog))) outcome
Proof
  rw []
  >> ‘outcome ≠ Fail’ by metis_tac []
  >> drule_all source_dceProofTheory.compile_semantics
  >> strip_tac
  >> ‘¬semantics_determ s env (source_dce$compile_decs prog) Fail’ by
       metis_tac [semantics_determ_deterministic]
  >> drule_all source_letProofTheory.compile_semantics
  >> strip_tac
  >> irule source_lift_constsProofTheory.compile_semantics
  >> simp []
  >> metis_tac [semantics_determ_deterministic]
QED

Theorem adjust_decs_compose:
  adjust_decs g2 C2 (adjust_decs g1 C1 eds) = adjust_decs (g2 o g1) C2 eds
Proof
  simp [adjust_decs_def, evalSemTheory.eval_decs_state_component_equality,
        FUN_EQ_THM, OPTION_MAP_COMPOSE]
QED

Theorem OPTION_MAP_adjust_es_compose:
  OPTION_MAP (adjust_es g2 C2) (OPTION_MAP (adjust_es g1 C1) x) =
  OPTION_MAP (adjust_es (g2 o g1) C2) x
Proof
  Cases_on ‘x’ >- simp []
  \\ rename1 ‘SOME e’
  \\ Cases_on ‘e’ \\ simp [adjust_es_def, adjust_decs_compose]
QED

Theorem OPTION_MAP_adjust_es_o:
  OPTION_MAP (adjust_es g2 C2) o OPTION_MAP (adjust_es g1 C1) =
  OPTION_MAP (adjust_es (g2 o g1) C2)
Proof
  simp [FUN_EQ_THM, OPTION_MAP_adjust_es_compose]
QED

Theorem inc_compile_eq:
  source_to_source$inc_compile =
    source_lift_consts$compile_decs o source_let$compile_decs
Proof
  simp [FUN_EQ_THM, source_to_sourceTheory.inc_compile_def]
QED

Theorem decs_factor_st_EvalDecs[local]:
  decs_factor_st g C s ⇒ ∀x. s.eval_state = SOME x ⇒ ∃ev. x = EvalDecs ev
Proof
  rw [decs_factor_st_def]
  \\ Cases_on ‘x’
  \\ gvs [decs_factor_es_def]
QED

(* the declarations given to Eval are compiled with inc_compile *)
Theorem inc_compile_semantics:
  decs_factor_st source_to_source$inc_compile C s ∧
  ¬semantics_determ s env prog Fail ∧
  semantics_determ s env prog outcome ⇒
    semantics_determ (s with eval_state updated_by
                        OPTION_MAP (adjust_es source_to_source$inc_compile C))
      env prog outcome
Proof
  rw [inc_compile_eq]
  \\ qabbrev_tac ‘C1 = λx. C (FST x, FST (SND x),
                             source_lift_consts$compile_decs (SND (SND x)))’
  \\ ‘decs_factor_st source_let$compile_decs C1 s’
    by (gvs [decs_factor_st_def]
        \\ Cases_on ‘s.eval_state’ \\ gvs [decs_factor_es_def]
        \\ rename1 ‘decs_factor_es _ _ (SOME e)’
        \\ Cases_on ‘e’ \\ gvs [decs_factor_es_def, decs_factor_def, Abbr ‘C1’])
  \\ drule_all source_letProofTheory.compile_semantics_decs
  \\ strip_tac
  \\ ‘outcome ≠ Fail’ by metis_tac []
  \\ qabbrev_tac ‘s1 = s with eval_state updated_by
                         OPTION_MAP (adjust_es source_let$compile_decs C1)’
  \\ ‘¬semantics_determ s1 env prog Fail’
    by metis_tac [semantics_determ_deterministic]
  \\ ‘decs_factor_st source_lift_consts$compile_decs C s1’
    by (gvs [Abbr ‘s1’, decs_factor_st_def]
        \\ Cases_on ‘s.eval_state’ \\ gvs [decs_factor_es_def]
        \\ rename1 ‘s.eval_state = SOME e’
        \\ Cases_on ‘e’
        \\ gvs [decs_factor_es_def, adjust_es_def, adjust_decs_def,
                decs_factor_def, Abbr ‘C1’])
  \\ drule_all source_lift_constsProofTheory.compile_semantics_decs
  \\ simp [Abbr ‘s1’, OPTION_MAP_adjust_es_o]
QED

Theorem compile_semantics:
  env.v = nsEmpty ∧
  decs_factor_st source_to_source$inc_compile C s ∧
  ¬semantics_determ s env prog Fail ∧
  semantics_determ s env prog outcome ⇒
    semantics_determ
      (s with eval_state updated_by
         OPTION_MAP (adjust_es source_to_source$inc_compile C))
      env (source_to_source$compile prog) outcome
Proof
  rw []
  \\ ‘outcome ≠ Fail’ by metis_tac []
  \\ drule decs_factor_st_EvalDecs
  \\ strip_tac
  \\ drule_all compile_decs_semantics
  \\ strip_tac
  \\ qabbrev_tac ‘prog1 = source_lift_consts$compile_decs
                           (source_let$compile_decs (source_dce$compile_decs prog))’
  \\ ‘¬semantics_determ s env prog1 Fail’
    by metis_tac [semantics_determ_deterministic]
  \\ drule_all inc_compile_semantics
  \\ simp [Abbr ‘prog1’, source_to_sourceTheory.compile_def]
QED
