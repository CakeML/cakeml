(**
  Define an interval semantics on the elementary functions
  of Dandelion. The function borrows the definitions and soundness
  proof of basic arithmetic from FloVer
**)
open realTheory realLib RealArith transcTheory;
open IntervalArithTheory sqrtApproxTheory IntervalValidationTheory;
open realPolyTheory transcLangTheory mcLaurinApproxTheory approxPolyTheory;
open bitArithLib;
open preambleDandelion;

val _ = new_theory "transcIntvSem";

Definition intvUop_def:
  intvUop (Neg:transcLang$unop) iv = negateInterval iv ∧
  intvUop Inv iv = invertInterval iv
End

Definition intvBop_def:
  intvBop (Add:transcLang$binop) iv1 iv2 = addInterval iv1 iv2 ∧
  intvBop Sub iv1 iv2 = subtractInterval iv1 iv2 ∧
  intvBop Mul iv1 iv2 = multInterval iv1 iv2 ∧
  intvBop Div iv1 iv2 = divideInterval iv1 iv2
End

Definition evalPolyIntv_def:
  evalPolyIntv [] iv = (0,0) ∧
  evalPolyIntv (c::cs) iv = intvBop Add (c,c) (intvBop Mul iv (evalPolyIntv cs iv))
End

Definition internalSteps_def:
  internalSteps:num = 40
End

Definition newtonIters_def:
  newtonIters:num = 6
End

Theorem pi_le_4:
  pi < 4
Proof
  ‘pi / 2 < 2’ by (assume_tac PI2_BOUNDS >> gs[])
  >> gs[real_div]
QED

(**
  compute an interval bound for a transcendental/ HOL4 uncomputable function.
  We include sqrt here as it cannot be evaluated in HOL4 directly.
  The newton approximation trick is borrowed from FloVer.
  As we have to validate the newton approximation afterwards, it may fail
  to compute an interval bound thus we return an option here.
  In practice, we have not yet encountered a case where 4 iterations where not
  sufficient in combination with the multiplications
**)
Definition getFunIv_def:
  getFunIv Exp iv =
    (let
      lbExp = evalPoly (expPoly internalSteps) (FST iv);
      ubExp = evalPoly (expPoly internalSteps) (SND iv) +
              if iv = (0, inv 2) then expErrSmall internalSteps
              else expErrBig (clg (abs (SND iv) * 2)) internalSteps;
    in
      SOME (lbExp, ubExp)) ∧
  getFunIv Sin iv = SOME (-1, 1) ∧
  getFunIv Cos iv = SOME (-1, 1) ∧
  getFunIv Tan iv = NONE ∧
  (** Very coarse, but this is as good as it gets with the rough bounds on pi/2 **)
  getFunIv Atn iv = SOME (-2, 2) ∧
  getFunIv Sqrt iv =
    (* we do a newton approximation of the lower and upper bounds,
    0 < FST iv has to be checked before *)
   ( let sqrtLo = newton newtonIters (FST iv * 0.99) (IVlo iv * 0.99);
        sqrtHi = newton newtonIters (SND iv * 1.01) (SND iv * 1.01);
        newIV = (sqrtLo, sqrtHi)
    in
      if (validate_newton_down sqrtLo (FST iv) ∧
          validate_newton_up sqrtHi (SND iv)) then
        SOME newIV
      else NONE)∧
   getFunIv Log iv =
    (let
      lbLog = evalPoly (compose (logPoly (internalSteps+1)) [-1;1]) (FST iv);
      ubLog = evalPoly (compose (logPoly (internalSteps + 1)) [-1;1]) (SND iv) +
              logErr iv (internalSteps+1);
    in
      SOME (lbLog, ubLog))
End

Definition interpIntv_def:
  interpIntv (Var x) (env:(string#(real#real)) list) =
  do xv <- FIND (λ (y, iv). y = x) env;
     return (VarAnn (SND xv) x);
  od ∧
  interpIntv (Cst c) env = SOME (CstAnn (c,c) c) ∧
  interpIntv (Uop uop t) env =
    do r <- interpIntv t env;
       assert ((~ (uop = Inv)) ∨ (SND (getAnn r) < 0 ∨ 0 < FST (getAnn r) ));
      return (UopAnn (intvUop uop (getAnn r)) uop r)
    od ∧
  interpIntv (Bop bop t1 t2) env =
    do
      r1 <- interpIntv t1 env;
      r2 <- interpIntv t2 env;
      iv1 <<- getAnn r1;
      iv2 <<- getAnn r2;
      assert (bop = Div ⇒ (SND iv2 < 0 ∨ 0 < FST iv2));
      return (BopAnn (intvBop bop iv1 iv2) bop r1 r2);
    od ∧
  interpIntv (Fun s t) env =
    do
      r <- interpIntv t env;
      iv <<- getAnn r;
      (* Sqrt defined for positive values only *)
      assert ((~ (s = Sqrt)) ∨ (0 < FST iv));
      (* Tan cannot be done at 0 because we approximate it with sin x/cos x *)
      assert ((~ (s = Tan)) ∨ (SND iv < 0 ∨ 0 < FST iv));
      (* Log defined for positive values only *)
      assert ((~ (s = Log)) ∨ (1 < FST iv));
      ivRes <- getFunIv s iv;
      return (FunAnn ivRes s r);
    od ∧
  interpIntv (Poly p t) env =
    do
      r <- interpIntv t env;
      iv <<- getAnn r;
      return (PolyAnn (evalPolyIntv p iv) p r);
    od
End

Definition varsContained_def:
  varsContained (cenv:(string#real) list) (ivenv:(string#(real#real)) list) =
  ∀ x xiv.
    FIND (λ (y,r). y = x) ivenv = SOME xiv ⇒
    ∃ xr.
      FIND (λ (y,r). y = x) cenv = SOME xr ∧
      FST (SND xiv) ≤ SND xr ∧ SND xr ≤ SND (SND xiv)
End

Theorem evalPolyIntv_sound:
  ∀ p x iv.
    FST iv ≤ x ∧
    x ≤ SND iv ⇒
    FST (evalPolyIntv p iv) ≤ evalPoly p x ∧
    evalPoly p x ≤ SND (evalPolyIntv p iv)
Proof
  Induct_on ‘p’ >> gs[evalPolyIntv_def, evalPoly_def]
  >> rpt strip_tac
  >> first_x_assum $ drule_then $ drule_then assume_tac
  >> ‘contained (evalPoly p x) (evalPolyIntv p iv)’ by gs[contained_def]
  >> ‘contained x iv’ by gs[contained_def]
  >> pop_assum $ mp_then Any mp_tac interval_multiplication_valid
  >> disch_then (fn th => pop_assum $ mp_then Any mp_tac th)
  >> qspec_then ‘h’ (assume_tac o SIMP_RULE std_ss [pointInterval_def]) validPointInterval
  >> pop_assum $ mp_then Any mp_tac (SIMP_RULE std_ss [validIntervalAdd_def] interval_addition_valid)
  >> disch_then (fn th => disch_then $ mp_then Any mp_tac th)
  >> strip_tac >> gs[contained_def, intvBop_def]
QED

Definition validIVAnnot_def:
  validIVAnnot tAnn ivenv =
  ((∀ cenv.
    varsContained cenv ivenv ⇒
    ∃ r. interp (erase tAnn) cenv = SOME r ∧
    FST (getAnn tAnn) ≤ r ∧
    r ≤ SND (getAnn tAnn)) ∧
  (case tAnn of
    | CstAnn _ _ => T
    | VarAnn _ _ => T
    | UopAnn _ u e =>
        (u = Inv ⇒ SND (getAnn e) < 0 ∨ 0 < FST (getAnn e)) ∧
        validIVAnnot e ivenv
    | BopAnn _ b e1 e2 =>
        (b = Div ⇒ (SND (getAnn e2) < 0 ∨ 0 < FST (getAnn e2))) ∧
        validIVAnnot e1 ivenv ∧ validIVAnnot e2 ivenv
    | FunAnn _ _ e => validIVAnnot e ivenv
    | PolyAnn _ _ e => validIVAnnot e ivenv))
End

Theorem validIVAnnot_single:
  validIVAnnot tAnn ivenv ⇒
  ∀ cenv.
    varsContained cenv ivenv ⇒
    ∃ r. interp (erase tAnn) cenv = SOME r ∧
    FST (getAnn tAnn) ≤ r ∧
    r ≤ SND (getAnn tAnn)
Proof
  gs[Once validIVAnnot_def] >> metis_tac[]
QED

Theorem interpIntv_sound:
  ∀ t ivenv tAnn.
    interpIntv t ivenv = SOME tAnn ⇒
    validIVAnnot tAnn ivenv
Proof
  Induct_on ‘t’ >> simp[interpIntv_def, Once validIVAnnot_def]
  >> rpt strip_tac
  >- (
    last_x_assum $ mpx_with_then assume_tac ‘interpIntv t ivenv = _’
    >> mp_with_then (mpx_with_then strip_assume_tac ‘varsContained _ _’) ‘validIVAnnot r _’ validIVAnnot_single
    >> Cases_on ‘t0’ >> gs[getFun_def, getFunIv_def]
    >> rpt VAR_EQ_TAC >> gs[SIN_BOUNDS, COS_BOUNDS, erase_def, getAnn_def, interp_def, getFun_def]
    (* exp *)
    >- (
      conj_tac
      (* lower bound *)
      >- (
        irule REAL_LE_TRANS >> qexists_tac ‘exp (FST (getAnn r))’
        >> gs[EXP_MONO_LE]
        >> qspecl_then [‘FST (getAnn r)’, ‘internalSteps’] strip_assume_tac  MCLAURIN_EXP_LE
        >> pop_assum $ rewrite_tac o single
        >> gs[exp_sum_to_poly]
        >> irule REAL_LE_MUL
        >> gs[POW_POS, internalSteps_def]
        >> irule REAL_LE_MUL
        >> gs[EXP_POS_LE])
      (* upper bound *)
      >> irule REAL_LE_TRANS >> qexists_tac ‘exp (SND (getAnn r))’
      >> gs[EXP_MONO_LE]
      >> qspecl_then [‘SND (getAnn r)’, ‘internalSteps’] strip_assume_tac  MCLAURIN_EXP_LE
      >> pop_assum $ rewrite_tac o single
      >> gs[exp_sum_to_poly]
      >> qmatch_goalsub_abbrev_tac ‘exp_err ≤ _’
      >> irule REAL_LE_TRANS >> qexists_tac ‘abs exp_err’ >> gs[ABS_LE]
      >> unabbrev_all_tac
      >> Cases_on ‘getAnn r = (0, inv 2)’
      >> asm_rewrite_tac[expErrSmall_def, GSYM real_div]
      >- (
        irule exp_remainder_bounded_small
        >> Cases_on ‘r’ >> gs[internalSteps_def]
        >> gs[abs] >> every_case_tac >> real_tac)
      >> asm_rewrite_tac[expErrBig_def]
      >> irule exp_remainder_bounded_big
      >> qmatch_goalsub_abbrev_tac ‘abs (SND (getAnn r)) ≤ upExp’
      >> ‘abs (SND (getAnn r)) ≤ upExp’
        by (
          unabbrev_all_tac
          >> cond_cases_tac >> gs[]
          >- (pop_assum $ rewrite_tac o single o GSYM >> gs[])
          >> irule REAL_LE_TRANS >> qexists_tac ‘&clg (2 * abs (SND (getAnn r)))’
          >> gs[LE_NUM_CEILING])
      >> rpt conj_tac >> TRY( gs[internalSteps_def] >> NO_TAC)
      >> irule REAL_LE_TRANS
      >> qexists_tac ‘abs t’ >> gs[ABS_LE]
      >> irule REAL_LE_TRANS >> qexists_tac ‘abs (SND (getAnn r))’ >> gs[])
    (* atn *)
    >- (
      rpt conj_tac
      >> qspec_then ‘r'’ strip_assume_tac ATN_BOUNDS
      >> strip_assume_tac PI2_BOUNDS
      >> irule REAL_LE_TRANS
      >- (
        qexists_tac ‘- (pi/2)’ >> conj_tac
        >> real_tac)
      >> qexists_tac ‘pi/2’ >> conj_tac
      >> real_tac)
    (* sqrt *)
    >- ( first_x_assum $ mp_then Any mp_tac validate_newton_lb_valid
         >> impl_tac >> gs[]
         >- (
         reverse conj_tac >- real_tac
         >> irule newton_method_pos >> conj_tac
         >> irule REAL_LE_MUL >> gs[] >> real_tac)
         >> first_x_assum $ mp_then Any mp_tac validate_newton_ub_valid
         >> impl_tac >> gs[]
         >- (
         reverse conj_tac >- real_tac
         >> irule newton_method_pos >> conj_tac
         >> irule REAL_LE_MUL >> gs[] >> real_tac)
         >> rpt strip_tac
         >> irule REAL_LE_TRANS
         THENL [
           qexists_tac ‘sqrt (FST (getAnn r))’,
           qexists_tac ‘sqrt (SND (getAnn r))’]
         >> gs[]
         >> irule SQRT_MONO_LE >> real_tac)
       (* ln *)
    >> conj_tac
      (* lower bound *)
      >- (
        irule REAL_LE_TRANS >> qexists_tac ‘ln (FST (getAnn r))’
        >> ‘0 < r'’ by real_tac
        >> ‘0 < FST (getAnn r)’ by real_tac
        >> gs[LN_MONO_LE]
        >> qspecl_then [‘FST (getAnn r) - 1 ’, ‘internalSteps+1’] mp_tac  MCLAURIN_LN_POS
        >> impl_tac >- ( gs[internalSteps_def] >> real_tac )
        >> strip_tac
        >> ‘1 + (FST (getAnn r) − 1) = FST (getAnn r)’ by real_tac
        >> ‘0 < internalSteps+1’ by gs[internalSteps_def]
        >> gs[log_sum_to_poly_indexshift]
        >> irule REAL_LE_MUL
        >> conj_tac
        >- ( irule REAL_LE_MUL
             >> conj_tac
             >- gs[internalSteps_def]
             >> ‘1+t ≠ 0’ by real_tac
             >> gs[POW_INV]
             >> DISJ1_TAC >> real_tac
           )
        >> irule POW_POS >> real_tac)
    (* upper bound *)
    >> irule REAL_LE_TRANS >> qexists_tac ‘ln (SND (getAnn r))’
    >> ‘0 < r'’ by real_tac
    >> ‘0 < SND (getAnn r)’ by real_tac
    >> gs[LN_MONO_LE]
    >> qspecl_then [‘SND (getAnn r) - 1 ’, ‘internalSteps+1’] mp_tac  MCLAURIN_LN_POS
    >> impl_tac >- ( gs[internalSteps_def] >> real_tac )
    >> strip_tac
    >> pop_assum mp_tac
    >> ‘1 + (SND (getAnn r) − 1) = SND (getAnn r)’ by real_tac
    >> asm_rewrite_tac[]
    >> disch_then $ once_rewrite_tac o single
    >> ‘0 < internalSteps+1’ by gs[internalSteps_def]
    >> pop_assum $ mp_then Any mp_tac log_sum_to_poly_indexshift
    >> disch_then $ once_rewrite_tac o single
    >> irule REAL_LE_LADD_IMP
    >> rewrite_tac[logErr_def, internalSteps_def]
    >> rewrite_tac[EVAL“-1 pow SUC (40 + 1)”, REAL_MUL_LID, real_div, ABS_MUL, GSYM POW_ABS]
    >> irule REAL_LE_MUL2
    >> gs[] >> rpt conj_tac
    >- (irule POW_LE >> conj_tac >> real_tac)
    >- (rewrite_tac[abs] >> gs[REAL_INV_MUL']
        >> ‘inv (1 + t) ≤ 1’ by (
          once_rewrite_tac[GSYM REAL_INV1]
          >> irule REAL_LE_INV2 >> gs[] >> real_tac)
        >> once_rewrite_tac [GSYM $ EVAL “1 pow 41”]
        >> irule POW_LE >> gs[]
        >> real_tac)
    >- ( real_tac )
    >> real_tac)
  >- (rpt VAR_EQ_TAC >> gs[])
  >- (
    last_x_assum $ mpx_with_then assume_tac ‘interpIntv _ _ = _’
    >> mp_with_then (mpx_with_then strip_assume_tac ‘varsContained cenv ivenv’) ‘validIVAnnot _ _’ validIVAnnot_single
    >> rpt VAR_EQ_TAC >> gs[erase_def, getAnn_def, interp_def]
    >> drule_then drule evalPolyIntv_sound
    >> disch_then $ qspec_then ‘l’ assume_tac
    >> gs[])
  >- (rpt VAR_EQ_TAC >> gs[])
  >- (
    rpt VAR_EQ_TAC >> gs[getAnn_def, erase_def, interp_def, PULL_EXISTS]
    >> last_x_assum $ mpx_with_then assume_tac ‘interpIntv t _ = _’
    >> last_x_assum $ mpx_with_then assume_tac ‘interpIntv t' _ = _’
    >> ntac 2 (pop_assum $ mp_then Any (mp_with_then mp_tac ‘varsContained cenv ivenv’) validIVAnnot_single)
    >> rpt strip_tac >> gs[]
    >> Cases_on ‘b’ >> gs[intvBop_def]
    >- (
      qspecl_then [‘getAnn r1’, ‘getAnn r2’] mp_tac interval_addition_valid
      >> gs[validIntervalAdd_def, contained_def, appBop_def]
      >> rpt $ disch_then drule)
    >- (
      qspecl_then [‘getAnn r1’, ‘getAnn r2’] mp_tac interval_subtraction_valid
      >> gs[validIntervalSub_def, contained_def, appBop_def]
      >> rpt $ disch_then drule)
    >- (
      qspecl_then [‘getAnn r1’, ‘getAnn r2’] mp_tac interval_multiplication_valid
      >> gs[contained_def, appBop_def])
    >> conj_tac
    >> TRY (qspecl_then [‘getAnn r1’, ‘getAnn r2’] mp_tac interval_division_valid
    >> gs[contained_def, appBop_def] >> NO_TAC)
    >> CCONTR_TAC >> gs[] >> rpt VAR_EQ_TAC
    >> ‘0 < 0’ suffices_by gs[] >> real_tac)
  >- (rpt VAR_EQ_TAC >> gs[])
  >- (
    rpt VAR_EQ_TAC >> gs[getAnn_def, erase_def, interp_def, PULL_EXISTS]
    >> last_x_assum $ mpx_with_then assume_tac ‘interpIntv t _ = _’
    >> pop_assum $ mp_then Any (mp_with_then strip_assume_tac ‘varsContained cenv ivenv’) validIVAnnot_single
    >> Cases_on ‘u’ >> gs[interp_def, intvUop_def, appUop_def]
    >- (
      qspec_then ‘getAnn r’ mp_tac interval_negation_valid
      >> gs[contained_def])
    >> qspec_then ‘getAnn r’ assume_tac interval_inversion_valid
    >> gs[contained_def]
    >> CCONTR_TAC >> gs[] >> rpt VAR_EQ_TAC
    >> ‘0 < 0’ suffices_by gs[] >> real_tac)
  >> rpt VAR_EQ_TAC
  >> gs[interp_def, erase_def, getAnn_def, varsContained_def, PULL_EXISTS]
QED

Definition sqrtReplace_def:
  sqrtReplace (VarAnn iv x) = SOME (Var x) ∧
  sqrtReplace (CstAnn iv c) = SOME (Cst c) ∧
  sqrtReplace (UopAnn iv u e) =
    do
      eRepl <- sqrtReplace e;
      return (Uop u eRepl);
    od ∧
  sqrtReplace (BopAnn iv b e1 e2) =
    do
      e1Repl <- sqrtReplace e1;
      e2Repl <- sqrtReplace e2;
      return (Bop b e1Repl e2Repl);
    od ∧
  sqrtReplace (PolyAnn iv p e)=
    do
      eRepl <- sqrtReplace e;
      return (Poly p eRepl);
    od ∧
  sqrtReplace ((FunAnn iv f e):(real#real)approxAnn) =
    do
      eRepl <- sqrtReplace e;
      if (f = Sqrt ∧ 1 < FST (getAnn e) ∧ 1 < SND (getAnn e))
      then return (Fun Exp (Bop Mul (Fun Log eRepl) (Cst (inv 2))))
      else return (Fun f eRepl)
    od
End

(** TODO Make this an equivalence **)
Theorem sqrtReplace_sound:
 ∀ tr tr' r ivenv cenv.
   sqrtReplace tr = SOME tr'∧
   validIVAnnot tr ivenv ∧
   interp (erase tr) cenv = SOME r ∧
   varsContained cenv ivenv ⇒
   interp tr' cenv = SOME r
Proof
  Induct_on ‘tr’ >> simp[sqrtReplace_def, SimpL“$==>”, erase_def, interp_def, Once validIVAnnot_def]
  >> rpt strip_tac
  >> first_x_assum $ mp_with_then strip_assume_tac ‘varsContained _ _’
  >- (
    qpat_x_assum ‘_ = SOME tr'’ mp_tac
    >> cond_cases_tac >> gs[] >> strip_tac
    >> rpt VAR_EQ_TAC
    >- (
      last_x_assum $ drule_then drule >> gs[]
      >> strip_tac
      >> simp[interp_def, getFun_def, appBop_def]
      >> mpx_with_then assume_tac ‘validIVAnnot tr ivenv’ validIVAnnot_single
      >> pop_assum $ drule_then strip_assume_tac
      >> gs[] >> VAR_EQ_TAC
      >> ‘1 < r’ by real_tac
      >> ‘0 < r’ by real_tac
      >> mpx_with_then assume_tac ‘0 < r’ SQRT_EXPLN_GENERAL
      >> gs[]
      >> ‘1/2 * ln r = ln r / 2’ by gs[]
      >> pop_assum $ rewrite_tac o single)
    >> last_x_assum $ drule_then drule >> gs[]
    >> strip_tac >> gs[interp_def])
  >> rpt (first_x_assum $ dxrule_then $ dxrule_then dxrule  >> gs[]
         >> strip_tac)
  >> rpt VAR_EQ_TAC
  >> gs[interp_def, erase_def]
QED

(** Version computing bounds:

Definition sqrtReplace_def:
  sqrtReplace (VarAnn iv x) = SOME (VarAnn iv x) ∧
  sqrtReplace (CstAnn iv c) = SOME (CstAnn iv c) ∧
  sqrtReplace (UopAnn iv u e) =
    do
      eRepl <- sqrtReplace e;
      return (UopAnn iv u eRepl);
    od ∧
  sqrtReplace (BopAnn iv b e1 e2) =
    do
      e1Repl <- sqrtReplace e1;
      e2Repl <- sqrtReplace e2;
      return (BopAnn iv b e1Repl e2Repl);
    od ∧
  sqrtReplace (PolyAnn iv p e)=
    do
      eRepl <- sqrtReplace e;
      return (PolyAnn iv p eRepl);
    od ∧
  sqrtReplace ((FunAnn iv f e):(real#real)approxAnn) =
    do
      eRepl <- sqrtReplace e;
      if (f = Sqrt ∧ 1 < FST (getAnn e) ∧ 1 < SND (getAnn e))
      then
        do
          assert (1 < FST (getAnn eRepl));
          ivLog <- getFunIv Log iv;
          ivMul <<- intvBop Mul ivLog (inv 2, inv 2);
          ivExp <- getFunIv Exp ivMul;
          return (FunAnn ivExp Exp (BopAnn ivMul Mul (FunAnn ivLog Log eRepl) (CstAnn (inv 2, inv 2) (inv 2))));
        od
      else return (FunAnn iv f eRepl)
    od
End
**)

val _ = export_theory();
