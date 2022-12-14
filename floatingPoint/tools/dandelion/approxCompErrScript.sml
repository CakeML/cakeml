(**
  Theorems about how to compose errors from truncated Taylor series
  for each supported elementary function
**)
open IntervalArithTheory ErrorValidationTheory sqrtApproxTheory;
open moreRealTheory mcLaurinApproxTheory realPolyTheory realPolyProofsTheory
     transcLangTheory approxPolyTheory transcIntvSemTheory;
open preambleDandelion;

val _ = new_theory "approxCompErr";

Theorem MCLAURIN_EXP_COMPOSITE_ERR:
  ∀  x y err lb ub errExpUb errExpY p.
    0 ≤ err ∧
    err ≤ inv 2 ∧ (* the error is reasonably small *)
    abs (x - y) ≤ err ∧
    lb ≤ x ∧ x ≤ ub ∧
    abs (exp ub - evalPoly p ub) ≤ errExpUb ⇒
    abs (exp y - evalPoly p y) ≤ errExpY ⇒
    abs (exp x - evalPoly p y) ≤
      errExpY + (* Exp error *)
      (evalPoly p ub + errExpUb)
         * (2 * err) (* propagated error from f *)
Proof
  rpt strip_tac >> drule MCLAURIN_EXP_COMPOSITE
  >> disch_then $ drule_then assume_tac
  >> transitivity_for ‘abs (exp x - exp y) + abs (exp y - evalPoly p y)’
  >> conj_tac
  >- (
    transitivity_for ‘abs (exp x - exp y + (exp y - evalPoly p y))’
    >> conj_tac  >> real_tac)
  >> ‘&FACT n ≠ 0’ by (unabbrev_all_tac >> rpt $ pop_assum kall_tac >> Induct_on ‘n’ >> gs[FACT])
  >> ‘abs (inv (&FACT n)) = inv (&FACT n)’
     by (gs[abs])
  >> qmatch_goalsub_abbrev_tac ‘abs expProp + abs expNew’
  >> real_rw ‘abs expProp + abs expNew = abs expNew + abs expProp’
  >> irule REAL_LE_ADD2 >> conj_tac
  (* New error *)
  >- ( unabbrev_all_tac >> gs[])
  >> transitivity_for ‘exp x * (exp err - 1)’ >> gs[]
  >> transitivity_for ‘exp x * (1 + 2 * err - 1)’ >> conj_tac
  >- (
    irule REAL_LE_LMUL_IMP >> gs[EXP_POS_LE, real_sub]
    >> irule REAL_EXP_BOUND_LEMMA >> gs[])
  >> real_rw ‘1 + 2 * err - 1 = 2 * err’
  >> real_rw ‘exp x * (2 * err) = 2 * (err * exp x)’
  >> ntac 2 $ (irule REAL_LE_LMUL_IMP >> gs[])
  >> transitivity_for ‘exp ub’ >> gs[EXP_MONO_LE]
  >> real_tac
QED

Theorem MCLAURIN_SIN_COMPOSITE_ERR:
  ∀ x y err iv steps polySin errSin polyCos errCos p errSinY.
  0 ≤ err ∧ err ≤ inv 2 ∧
  abs (x - y) ≤ err ∧
  approxPolySideCond steps ∧
  approxPoly Sin (0, err) steps = SOME (polySin, errSin) ∧
  approxPoly Cos (0, err) steps = SOME (polyCos, errCos) ∧
  abs (sin y - evalPoly p y) ≤ errSinY ⇒
  abs (sin x - evalPoly p y) ≤
    errSinY +
      (abs (evalPoly polyCos err - errCos - 1) + evalPoly polySin err + errSin)
Proof
  rpt strip_tac >> drule MCLAURIN_SIN_COMPOSITE
  >> ‘err ≤ pi / 2’
    by (irule REAL_LE_TRANS >> qexists_tac ‘inv 2’ >> gs[inv2_le_pi2])
  >> disch_then $ drule_then $ drule_then assume_tac
  >> real_rw ‘sin x - evalPoly p y = (sin y - evalPoly p y) + (sin x - sin y)’
  >> transitivity_for ‘abs (sin y - evalPoly p y) + abs (sin x - sin y)’
  >> conj_tac >- gs[REAL_ABS_TRIANGLE]
  >> irule REAL_LE_ADD2 >> conj_tac >- gs[]
  >> transitivity_for ‘abs (cos err - 1) + sin err’
  >> conj_tac >- gs[]
  >> rewrite_tac [GSYM REAL_ADD_ASSOC]
  >> drule approxPoly_soundness
  >> disch_then (fn th =>
                     qspec_then ‘Sin’ mp_tac th
                   >> qspec_then ‘Cos’ mp_tac th)
  >> disch_then $ drule_then $ qspec_then ‘err’ mp_tac
  >> impl_tac >- gs[]
  >> strip_tac
  >> disch_then $ drule_then $ qspec_then ‘err’ mp_tac
  >> impl_tac >- gs[]
  >> strip_tac >> gs[getFun_def]
  >> irule REAL_LE_ADD2 >> reverse conj_tac
  >- real_tac
  >> ‘evalPoly polyCos err - errCos ≤ cos err’ by real_tac
  >> ‘cos err ≤ 1’ by (gs[COS_BOUNDS])
  >> ‘cos err - 1 ≤ 0’ by real_tac
  >> ‘evalPoly polyCos err - errCos - 1 ≤ 0’ by real_tac
  >> rewrite_tac [GSYM abs_alt_abs]
  >> gs[abs_alt_def, real_sub]
QED

Theorem MCLAURIN_COS_COMPOSITE_ERR:
  ∀ x y err iv steps polySin errSin polyCos errCos p errCosY.
  0 ≤ err ∧ err ≤ inv 2 ∧
  abs (x - y) ≤ err ∧
  approxPolySideCond steps ∧
  approxPoly Sin (0, err) steps = SOME (polySin, errSin) ∧
  approxPoly Cos (0, err) steps = SOME (polyCos, errCos) ∧
  abs (cos y - evalPoly p y) ≤ errCosY ⇒
  abs (cos x - evalPoly p y) ≤
    errCosY +
      (abs (evalPoly polyCos err - errCos - 1) + evalPoly polySin err + errSin)
Proof
  rpt strip_tac >> drule MCLAURIN_COS_COMPOSITE
  >> ‘err ≤ pi / 2’
    by (irule REAL_LE_TRANS >> qexists_tac ‘inv 2’ >> gs[inv2_le_pi2])
  >> disch_then $ drule_then $ drule_then assume_tac
  >> real_rw ‘cos x - evalPoly p y = (cos y - evalPoly p y) + (cos x - cos y)’
  >> transitivity_for ‘abs (cos y - evalPoly p y) + abs (cos x - cos y)’
  >> conj_tac >- gs[REAL_ABS_TRIANGLE]
  >> irule REAL_LE_ADD2 >> conj_tac >- gs[]
  >> transitivity_for ‘abs (cos err - 1) + sin err’
  >> conj_tac >- gs[]
  >> rewrite_tac [GSYM REAL_ADD_ASSOC]
  >> drule approxPoly_soundness
  >> disch_then (fn th =>
                     qspec_then ‘Sin’ mp_tac th
                   >> qspec_then ‘Cos’ mp_tac th)
  >> disch_then $ drule_then $ qspec_then ‘err’ mp_tac
  >> impl_tac >- gs[]
  >> strip_tac
  >> disch_then $ drule_then $ qspec_then ‘err’ mp_tac
  >> impl_tac >- gs[]
  >> strip_tac >> gs[getFun_def]
  >> irule REAL_LE_ADD2 >> reverse conj_tac
  >- real_tac
  >> ‘evalPoly polyCos err - errCos ≤ cos err’ by real_tac
  >> ‘cos err ≤ 1’ by (gs[COS_BOUNDS])
  >> ‘cos err - 1 ≤ 0’ by real_tac
  >> ‘evalPoly polyCos err - errCos - 1 ≤ 0’ by real_tac
  >> rewrite_tac [GSYM abs_alt_abs]
  >> gs[abs_alt_def, real_sub]
QED

Theorem MCLAURIN_LN_COMPOSITE_ERR:
  ∀ x y z err iv steps polyLn errLn p errLnY.
  0 ≤ err ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
  abs (x - y) ≤ err ∧ z ≤ min x y ∧
  approxPolySideCond steps ∧
  approxPoly Log (1 + err/z, 1 + err/z) steps = SOME (polyLn, errLn) ⇒
  abs (ln y - evalPoly p y) ≤ errLnY ⇒
  abs (ln x - evalPoly p y) ≤
    errLnY + (evalPoly polyLn (1 + err/z) + errLn)
Proof
  rpt strip_tac >> drule MCLAURIN_LN_COMPOSITE
  >> disch_then $ qspecl_then [‘x’, ‘y’] mp_tac
  >> impl_tac >- gs[]
  >> strip_tac
  >> real_rw ‘ln x - evalPoly p y = (ln y - evalPoly p y) + (ln x - ln y)’
  >> transitivity_for ‘abs (ln y - evalPoly p y) + abs (ln x - ln y)’
  >> conj_tac >- gs[REAL_ABS_TRIANGLE]
  >> irule REAL_LE_ADD2 >> conj_tac >- gs[]
  >> transitivity_for ‘abs (ln (1 + err / min x y))’
  >> conj_tac >- gs[]
  >> ‘0 < min x y ’ by (gs[min_def] >> cond_cases_tac >> gs[])
  >> ‘0 ≤ err / min x y’ by (gs[nonzerop_def] >> cond_cases_tac >> gs[])
  >> ‘1 ≤ 1 + err / min x y’ by real_tac
  >> ‘0 ≤ ln (1 + err / min x y)’ by gs[LN_POS]
  >> gs[abs]
  >> irule REAL_LE_TRANS
  >> qexists_tac ‘ln (1 + err / z)’ >> conj_tac
  >- (
    ‘0 ≤ err / z’ by (gs[nonzerop_def] >> cond_cases_tac >> gs[])
    >> ‘0 < 1 + err / z’ by real_tac
    >> Cases_on ‘err = 0’ >> gs[LN_1]
    >> ‘0 < err / min x y’ by (gs[nonzerop_def] >> cond_cases_tac >> gs[] >> real_tac)
    >> ‘0 < 1 + err / min x y’ by real_tac
    >> gs[LN_MONO_LE])
  >> drule approxPoly_soundness
  >> disch_then drule
  >> disch_then $ qspec_then ‘1 + err / z’ mp_tac >> impl_tac >- gs[]
  >> gs[getFun_def]
  >> disch_then $ mp_then Any assume_tac ERR_ABS_SIMP
  >> gs[]
QED

val _ = export_theory();
