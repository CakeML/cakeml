(*source_weakenletTheory
  Correctness for the source_letweaken pass.
 *)
Theory source_weakenletProof
Ancestors
  source_weakenlet evaluate evaluateProps semanticPrimitives
  semanticPrimitivesProps misc[qualified] semantics ast
  source_evalProof
Libs
  preamble


Triviality compile_decs_cons:
 !d ds.compile_decs (d ::ds) = HD (compile_decs [d]) :: compile_decs ds
Proof
  Induct_on `ds` >> rw[compile_decs_def] >>
  rpt (TOP_CASE_TAC >> simp[])
QED

Triviality compile_decs_sing_HD:
  !ds. [HD (compile_decs [ds])] = compile_decs [ds]
Proof
  Induct_on `ds`  >> rw[compile_decs_def] >>
  rpt (TOP_CASE_TAC >> simp[])
QED

(*TODO this is false the results needs to be weakened to an
  equivalence relation*)
Theorem compile_decs_correct:
  ∀s env ds s' res.
    evaluate_decs s env ds = (s', res) ∧
    res ≠ Rerr (Rabort Rtype_error) ⇒
      evaluate_decs s env (compile_decs ds) = (s', res)
Proof
  ho_match_mp_tac evaluate_decs_ind \\ rw [Once compile_decs_def]
  >~ [‘d1::d2::ds’] >- (
    qpat_x_assum ‘evaluate_decs _ _ _ = _’ mp_tac
    \\ simp [Once evaluate_decs_def]
    \\ disch_then (strip_assume_tac o SRULE[AllCaseEqs()])
    \\ gvs[]
    \\ simp[Once compile_decs_cons,compile_decs_sing_HD]
    \\ simp[Once evaluate_decs_cons,compile_decs_sing_HD]
    \\ fs[ combine_dec_result_eq_Rerr])
  >~ [‘[Dmod _ _]’] >- (
    gvs [compile_decs_def,evaluate_decs_def,AllCaseEqs()])
  >~ [‘[Dlocal _ _]’] >- (
    gvs [compile_decs_def,evaluate_decs_def,AllCaseEqs()])
  >~ [‘[Dletrec _ _]’] >- (
    gvs [compile_decs_def] >>    
    TOP_CASE_TAC  >- fs[] >>
    reverse TOP_CASE_TAC  >- fs[] >>
    `? fun_name first_arg exp.h = (fun_name,first_arg,exp)`
       by (PairCases_on `h` >> simp_tac(srw_ss())[]) >>
     POP_ASSUM SUBST_ALL_TAC >> simp[]
     TOP_CASE_TAC >> cheat)
  >> fs[compile_decs_def]
QED
