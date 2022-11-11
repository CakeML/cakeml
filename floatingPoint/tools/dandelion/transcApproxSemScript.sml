(**
  Define an "approximating" semantics on the elementary functions
  of Dandelion. The function approxTransc corresponds to the
  function "approxAsPoly" in the paper
**)
open realTheory realLib RealArith transcTheory;
open IntervalArithTheory ErrorValidationTheory sqrtApproxTheory;
open realPolyTheory transcLangTheory approxPolyTheory transcIntvSemTheory approxCompErrTheory;
open bitArithLib;
open preambleDandelion;

val _ = new_theory "transcApproxSem";

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "option";

Datatype:
  approxCfg =
  <| steps: num;
  |>
End

Definition errorPropBop_def:
  errorPropBop Add (iv1:(real#real)) e1 (iv2:(real#real)) (e2:real) = e1 + e2 ∧
  errorPropBop Sub iv1 e1 iv2 e2 = e1 + e2 ∧
  errorPropBop Mul iv1 e1 iv2 e2 = maxAbs iv1 * e2 + maxAbs iv2 * e1 + e1 * e2 ∧
  errorPropBop Div iv1 e1 iv2 e2 =
    maxAbs iv1 *
    (1 /
     (minAbsFun (widenInterval iv2 e2) *
      minAbsFun (widenInterval iv2 e2)) * e2) +
    maxAbs (invertInterval iv2) * e1 +
    e1 *
    (1 /
     (minAbsFun (widenInterval iv2 e2) *
      minAbsFun (widenInterval iv2 e2)) * e2)
End

Definition errorPropUop_def:
  errorPropUop (Neg:transcLang$unop) (iv:(real#real)) e:real = e ∧
  errorPropUop Inv iv e =
    (1 /
     (minAbsFun (widenInterval iv e) *
      minAbsFun (widenInterval iv e)) * e)
End

Definition errorPropSinCos_def:
  errorPropSinCos cfg iv err =
    if approxPolySideCond cfg.steps
    then
      case approxPoly Cos (0,err) cfg.steps of
      | NONE => NONE
      | SOME (polyCos, errCos) =>
        case approxPoly Sin (0,err) cfg.steps of
        | NONE => NONE
        | SOME (polySin, errSin) =>
          SOME (abs ((evalPoly polyCos err - errCos) - 1) + evalPoly polySin err + errSin)
    else NONE
End

Definition errorPropFun_def:
  errorPropFun Exp cfg (iv:real#real) (err:real) (pWiden:poly) (errPWiden:real) =
    SOME (
      errPWiden + (* Exp error *)
        (evalPoly pWiden (SND iv) + errPWiden)
          * (2 * err)) (* propagated error from f *)
  ∧
  errorPropFun Sin cfg (iv:real#real) (err:real) (pWiden:poly) (errPWiden:real) =
    (case errorPropSinCos cfg iv err of
     | NONE => NONE
     | SOME propErr =>  SOME (errPWiden + propErr))
  ∧
  errorPropFun Cos cfg (iv:real#real) (err:real) (pWiden:poly) (errPWiden:real) =
    (case errorPropSinCos cfg iv err of
     | NONE => NONE
     | SOME propErr =>  SOME (errPWiden + propErr))
  ∧
  errorPropFun Log cfg iv err pWiden errPWiden =
    (if approxPolySideCond cfg.steps ∧ 0 < FST (widenInterval iv err)
    then
      case approxPoly Log (1 + err / FST (widenInterval iv err), 1 + err / FST (widenInterval iv err)) cfg.steps of
      | NONE => NONE
      | SOME (p, errP) =>
          SOME (errPWiden + (evalPoly p (1 + err/FST (widenInterval iv err)) + errP))
    else NONE)
  ∧
  errorPropFun _ _ _ _ _ _ = NONE (** TODO **)
End

Definition isVar_def:
  isVar e = case e of |VarAnn iv s => T |_ => F
End

Definition approxTransc_def:
  (** Constants and variables are always exact **)
  approxTransc cfg (VarAnn iv s) = SOME (VarAnn 0 s) ∧
  approxTransc cfg (CstAnn iv r) = SOME (CstAnn 0 r) ∧
  (** Binary operators have to propagate errors on the arguments **)
  approxTransc cfg (BopAnn iv b e1 e2) =
    do
      e1Appr <- approxTransc cfg e1;
      e2Appr <- approxTransc cfg e2;
      assert (b = Div ⇒
              SND (widenInterval (getAnn e2) (getAnn e2Appr)) < 0 ∨
              0 < FST (widenInterval (getAnn e2) (getAnn e2Appr)));
      propError <<- errorPropBop b (getAnn e1) (getAnn e1Appr) (getAnn e2) (getAnn e2Appr);
      return (BopAnn propError b e1Appr e2Appr);
    od ∧
  approxTransc cfg (UopAnn iv u e) =
    do
      eAppr <- approxTransc cfg e;
      assert (u = Inv ⇒
              SND (widenInterval (getAnn e) (getAnn eAppr)) < 0 ∨
              0 < FST (widenInterval (getAnn e) (getAnn eAppr)));
      propError <<- errorPropUop u (getAnn e) (getAnn eAppr);
      return (UopAnn propError u eAppr);
    od ∧
  approxTransc cfg (FunAnn iv f e) =
  (do
    eAppr <- approxTransc cfg e; (* recursive call *)
    (if isVar e ∨ getAnn eAppr = 0 then
       do
         (* approximate polynomial on widened interval *)
         (pWiden,errWiden) <-
         approxPoly f (widenInterval (getAnn e) (getAnn eAppr) ) cfg.steps;
         steps <<- cfg.steps;
         assert (approxPolySideCond steps ∧ getAnn eAppr ≤ inv 2 ∧ 0 ≤ getAnn eAppr);
         return (PolyAnn errWiden pWiden eAppr);
       od
     else
       do
         eAppr <- approxTransc cfg e; (* recursive call *)
         (* approximate polynomial on widened interval *)
         (pWiden,errWiden) <-
         approxPoly f (widenInterval (getAnn e) (getAnn eAppr) ) cfg.steps;
         steps <<- cfg.steps;
         assert (approxPolySideCond steps ∧ getAnn eAppr ≤ inv 2 ∧ 0 ≤ getAnn eAppr);
         fullError <- errorPropFun f cfg (getAnn e) (getAnn eAppr) pWiden errWiden;
         return (PolyAnn fullError pWiden eAppr);
       od)
  od) ∧
  (* We do not support partial approximations for now *)
  approxTransc cfg  (PolyAnn iv p e) = NONE
End

Theorem errorPropBop_sound:
  ∀ op r11 r12 r21 r22 iv1 iv2 err1 err2.
    FST iv1 ≤ r11 ∧ r11 ≤ SND iv1 ∧
    FST iv2 ≤ r12 ∧ r12 ≤ SND iv2 ∧
    (op = Div ⇒ noDivzero (SND iv2) (FST iv2)) ∧
    (op = Div ⇒ let newIv = widenInterval iv2 err2 in noDivzero (SND newIv) (FST newIv)) ∧
    abs (r11 - r21) ≤ err1 ∧
    abs (r12 - r22) ≤ err2 ⇒
    abs (appBop op r11 r12 - appBop op r21 r22) ≤
    errorPropBop op iv1 err1 iv2 err2
Proof
  rpt strip_tac >> Cases_on ‘op’ >> rewrite_tac[errorPropBop_def, appBop_def]
  >- (
    real_rw ‘r11 + r12 - (r21 + r22) = r11 - r21 + (r12 - r22)’
    >> transitivity_for ‘abs (r11 - r21) + abs (r12 - r22)’
    >> gs[REAL_ABS_TRIANGLE]
    >> irule REAL_LE_ADD2 >> gs[])
  >- (
    real_rw ‘r11 - r12 - (r21 - r22) = r11 - r21 - (r12 - r22)’
    >> gs[real_sub]
    >> transitivity_for ‘abs (r11 + - r21) + abs (- (r12 + - r22))’
    >> gs[REAL_ABS_TRIANGLE, real_sub]
    >> irule REAL_LE_ADD2 >> gs[])
  >- (
    PairCases_on ‘iv1’ >> PairCases_on ‘iv2’
    >> irule multiplicationErrorBounded >> gs[]
    >> conj_tac THENL
    [ transitivity_for ‘abs (r11 - r21)’,
      transitivity_for ‘abs (r12 - r22)’]
    >> gs[ABS_POS])
  >> PairCases_on ‘iv1’ >> PairCases_on ‘iv2’
  >> irule divisionErrorBounded >> gs[] >> rpt conj_tac
  >- (irule distance_gives_iv >> qexists_tac ‘r11’ >> gs[contained_def])
  >- (irule distance_gives_iv >> qexists_tac ‘r12’ >> gs[contained_def])
  THENL [
    transitivity_for ‘abs (r11 - r21)’,
    transitivity_for ‘abs (r12 - r22)’]
  >> gs[ABS_POS]
QED

Theorem errorPropUop_sound:
  ∀ op r1 r2 iv err.
  FST iv ≤ r1 ∧ r1 ≤ SND iv ∧
  (op = Inv ⇒ noDivzero (SND iv) (FST iv)) ∧
  (op = Inv ⇒ let newIv = widenInterval iv err in noDivzero (SND newIv) (FST newIv)) ∧
  abs (r1 - r2) ≤ err ⇒
  abs (appUop op r1 - appUop op r2) ≤
  errorPropUop op iv err
Proof
  rpt strip_tac >> Cases_on ‘op’ >> rewrite_tac [errorPropUop_def, appUop_def]
  >- (
    ‘abs (- r1 - -r2) = abs (r1 - r2)’ suffices_by gs[]
    >> real_tac)
  >> qspecl_then [‘1’, ‘1’, ‘1’, ‘FST iv’, ‘SND iv’, ‘r1’, ‘1’, ‘r2’, ‘0’, ‘err’] mp_tac divisionErrorBounded
  >> gs[] >> impl_tac
  >- (
    rpt conj_tac >> gs[]
    >- (transitivity_for ‘abs (r1 - r2)’ >> gs[])
    >- gs[contained_def, widenInterval_def]
    >> irule distance_gives_iv >> qexists_tac ‘r1’ >> gs[contained_def])
  >> rewrite_tac[REAL_INV_1OVER, EVAL “maxAbs (1,1)”, REAL_MUL_RID]
QED

Theorem approxTranscFun_sound:
  FST iv ≤ x ∧ x ≤ SND iv ∧
  err ≤ inv 2 ∧
  0 ≤ err ∧
  abs (x - y) ≤ err ∧
  errorPropFun f cfg iv err pWiden errPWiden = SOME fullErr ∧
  (∀ x. FST (widenInterval iv err) ≤ x ∧ x ≤ SND (widenInterval iv err) ⇒
        abs (getFun f x - evalPoly pWiden x) ≤ errPWiden) ⇒
  abs (getFun f x - evalPoly pWiden y) ≤ fullErr
Proof
  Cases_on ‘f’ >> rewrite_tac[getFun_def, errorPropFun_def, SOME_11]
  >> rpt strip_tac >> rpt VAR_EQ_TAC
  >~ [‘abs (exp _ - _)’]
  >- (
    irule MCLAURIN_EXP_COMPOSITE_ERR >> gs[PULL_EXISTS]
    >> qexists_tac ‘FST iv’ >> gs[] >> conj_tac
    >- (
      first_x_assum $ qspec_then ‘SND iv’ mp_tac
      >> impl_tac >> gs[widenInterval_def]
      >> transitivity_for ‘x’ >> gs[]
      >> transitivity_for ‘FST iv’ >> gs[] >> real_tac)
    >> first_x_assum $ qspec_then ‘y’ mp_tac >> impl_tac >> gs[]
    >> drule $ SIMP_RULE std_ss [AbbrevsTheory.IVlo_def, AbbrevsTheory.IVhi_def, contained_def] distance_gives_iv
    >> rpt $ disch_then drule >> gs[])
  >~ [‘abs (sin _ - _)’]
  >- (
    gs[CaseEq"option", CaseEq"prod", errorPropSinCos_def]
    >> rpt VAR_EQ_TAC
    >> irule MCLAURIN_SIN_COMPOSITE_ERR >> gs[PULL_EXISTS]
    >> qexists_tac ‘cfg.steps’ >> gs[]
    >> first_x_assum $ qspec_then ‘y’ mp_tac >> impl_tac >> gs[]
    >> drule $ SIMP_RULE std_ss [AbbrevsTheory.IVlo_def, AbbrevsTheory.IVhi_def, contained_def] distance_gives_iv
    >> rpt $ disch_then drule >> gs[])
  >~ [‘abs (cos _ - _)’]
  >- (
    gs[CaseEq"option", CaseEq"prod", errorPropSinCos_def]
    >> rpt VAR_EQ_TAC
    >> irule MCLAURIN_COS_COMPOSITE_ERR >> gs[PULL_EXISTS]
    >> qexists_tac ‘cfg.steps’ >> gs[]
    >> first_x_assum $ qspec_then ‘y’ mp_tac >> impl_tac >> gs[]
    >> drule $ SIMP_RULE std_ss [AbbrevsTheory.IVlo_def, AbbrevsTheory.IVhi_def, contained_def] distance_gives_iv
    >> rpt $ disch_then drule >> gs[])
  >~ [‘abs (ln _ - _)’]
  >- (
    gs[CaseEq"option", CaseEq"prod"]
    >> rpt VAR_EQ_TAC
    >> irule MCLAURIN_LN_COMPOSITE_ERR >> gs[PULL_EXISTS]
    >> qexists_tac ‘cfg.steps’ >> gs[]
    >> first_x_assum $ qspec_then ‘y’ mp_tac >> impl_tac >> gs[]
    >> drule $ SIMP_RULE std_ss [AbbrevsTheory.IVlo_def, AbbrevsTheory.IVhi_def, contained_def] distance_gives_iv
    >> rpt $ disch_then drule >> gs[]
    >> rpt strip_tac
    >- (
      irule REAL_LTE_TRANS >> qexists_tac ‘FST iv - err’
      >> gs[widenInterval_def] >> real_tac)
    >- (
      irule REAL_LTE_TRANS >> qexists_tac ‘FST iv - err’
      >> gs[widenInterval_def] >> real_tac)
    >> gs[min_def] >> cond_cases_tac >> gs[]
    >> irule REAL_LE_TRANS >> qexists_tac ‘FST iv - err’
    >> gs[widenInterval_def] >> real_tac)
  >~ [‘abs (tan _ - _)’]
  >- ( gs[] ) (* by contradiction *)
  >~ [‘abs (atan _ - _)’]
  >- gs[] (* by contradiction *)
  >~ [‘abs (sqrt _ - _)’]
  >- ( gs[] ) (* by contradiction *)
QED

Theorem approxTransc_sound:
  ∀ trIVAnn trErrAnn cfg ivenv.
    validIVAnnot trIVAnn ivenv ∧
    approxTransc cfg trIVAnn = SOME trErrAnn ⇒
    ∀ cenv.
      varsContained cenv ivenv ⇒
      ∃ r1 r2.
        interp (erase trIVAnn) cenv = SOME r1 ∧
        interp (erase trErrAnn) cenv = SOME r2 ∧
        abs (r1 - r2) ≤ getAnn trErrAnn
Proof
  Induct_on ‘trIVAnn’ >> simp[approxTransc_def, Once validIVAnnot_def]
  >> rpt strip_tac
  >~ [‘FunAnn iv f e’] (* Transcendental function case *)
  >- (
    (* Case distinction for special case *)
    Cases_on ‘isVar e ∨ getAnn eAppr = 0’ >> gs[]
    >> PairCases_on ‘x’ >> gs[] >> rpt VAR_EQ_TAC
    >> qpat_x_assum ‘∀ cenv. varsContained _ _ ⇒ _’ $
                    mp_with_then strip_assume_tac ‘varsContained _ _’
    >> gs[erase_def, getAnn_def, GSYM AND_IMP_INTRO]
    >> last_x_assum $ mp_with_then assume_tac ‘validIVAnnot _ _’
    >> pop_assum $ mp_with_then assume_tac ‘approxTransc _ _ = _’
    >> pop_assum $ mp_with_then strip_assume_tac ‘varsContained _ _’
    >> gs[interp_def] >> rpt VAR_EQ_TAC
    >> qpat_x_assum ‘validIVAnnot e _’ $ mp_then Any assume_tac validIVAnnot_single
    >> pop_assum $ mp_with_then strip_assume_tac ‘varsContained _ _’
    >> qpat_x_assum ‘approxPoly _ _ _ = _’ $ mp_then Any assume_tac approxPoly_soundness
    >> ‘r = r1’ by gs[]
    >> VAR_EQ_TAC
    >- (
      pop_assum drule >> disch_then $ qspec_then ‘r’ mp_tac
      >> ‘getAnn eAppr = 0’ by
        (gs[isVar_def] >> Cases_on ‘e’ >> gs[approxTransc_def]
         >> rpt VAR_EQ_TAC >> gs[getAnn_def])
      >> gs[]
      >> rpt VAR_EQ_TAC
      >> disch_then irule
      >> gs[widenInterval_def])
    >- (
      pop_assum drule >> disch_then $ qspec_then ‘r’ mp_tac
      >> gs[]
      >> rpt VAR_EQ_TAC
      >> disch_then irule
      >> gs[widenInterval_def])
    >> drule approxTranscFun_sound
    >> rpt $ disch_then drule
    >> impl_tac
    >- (rpt strip_tac >> first_x_assum irule >> gs[])
    >> gs[])
  >~ [‘BopAnn iv op e1 e2’]
  >- (
    gs[] >> rpt VAR_EQ_TAC
    >> qpat_x_assum ‘∀ cenv. varsContained _ _ ⇒ _’ $
                    mp_with_then strip_assume_tac ‘varsContained _ _’
    >> gs[erase_def, getAnn_def, GSYM AND_IMP_INTRO]
    >> last_x_assum $ mp_with_then assume_tac ‘validIVAnnot e1 _’
    >> pop_assum $ mpx_with_then assume_tac ‘approxTransc _ trIVAnn = _’
    >> pop_assum $ mp_with_then strip_assume_tac ‘varsContained _ _’
    >> last_x_assum $ mp_with_then assume_tac ‘validIVAnnot e2 _’
    >> pop_assum $ mpx_with_then assume_tac ‘approxTransc _ _ = _’
    >> pop_assum $ mp_with_then strip_assume_tac ‘varsContained _ _’
    >> gs[interp_def] >> rpt VAR_EQ_TAC
    >> qpat_x_assum ‘validIVAnnot e1 _’ $ mp_then Any assume_tac validIVAnnot_single
    >> pop_assum $ mp_with_then strip_assume_tac ‘varsContained _ _’
    >> qpat_x_assum ‘validIVAnnot e2 _’ $ mp_then Any assume_tac validIVAnnot_single
    >> pop_assum $ mp_with_then strip_assume_tac ‘varsContained _ _’
    >> gs[] >> rpt VAR_EQ_TAC >> conj_tac
    >- (
      ‘contained r2' (widenInterval (getAnn e2) (getAnn e2Appr))’
       by (irule distance_gives_iv >> qexists_tac ‘r'’ >> gs[contained_def])
      >> gs[contained_def]
      >> rpt strip_tac >> CCONTR_TAC >> gs[] >> rpt VAR_EQ_TAC
      >> ‘0 < 0’ suffices_by gs[]
      >> real_tac)
    >> irule errorPropBop_sound >> gs[AbbrevsTheory.noDivzero_def])
  >~ [‘UopAnn iv op e’]
  >- (
    gs[] >> rpt VAR_EQ_TAC
    >> qpat_x_assum ‘∀ cenv. varsContained _ _ ⇒ _’ $
                    mp_with_then strip_assume_tac ‘varsContained _ _’
    >> gs[erase_def, getAnn_def, GSYM AND_IMP_INTRO]
    >> last_x_assum $ mp_with_then assume_tac ‘validIVAnnot e _’
    >> pop_assum $ mpx_with_then assume_tac ‘approxTransc _ _ = _’
    >> pop_assum $ mp_with_then strip_assume_tac ‘varsContained _ _’
    >> qpat_x_assum ‘validIVAnnot e _’ $ mp_then Any assume_tac validIVAnnot_single
    >> pop_assum $ mp_with_then strip_assume_tac ‘varsContained _ _’
    >> ‘r' = r1’ by gs[]
    >> gs[interp_def] >> rpt VAR_EQ_TAC >> conj_tac
    >- (
      ‘contained r2 (widenInterval (getAnn e) (getAnn eAppr))’
       by (irule distance_gives_iv >> qexists_tac ‘r'’ >> gs[contained_def])
      >> gs[contained_def]
      >> rpt strip_tac >> CCONTR_TAC >> gs[] >> rpt VAR_EQ_TAC
      >> ‘0 < 0’ suffices_by gs[]
      >> real_tac)
    >> irule errorPropUop_sound >> gs[AbbrevsTheory.noDivzero_def])
  >~ [‘CstAnn iv c’]
  >- (res_tac >> gs[getAnn_def, erase_def, interp_def])
  >~ [‘VarAnn iv x’]
  >> res_tac >> gs[getAnn_def, erase_def, interp_def]
QED

Definition optionGet_def:
  optionGet x =
  case x of (SOME x) => x
End

Theorem optionGet_SOME:
  optionGet (SOME x) = x
Proof
  gs[optionGet_def]
QED

Theorem approxTransc_sound_single:
  LENGTH ivenv = 1 ∧
  validIVAnnot trIVAnn ivenv ∧
  approxTransc cfg trIVAnn = SOME trErrAnn ⇒
  ∀ x.
    FST (SND (HD ivenv)) ≤ x ∧ x ≤ SND (SND (HD ivenv)) ⇒
    abs ((optionGet (interp (erase trIVAnn) [(FST (HD ivenv), x)])) - (optionGet (interp (erase trErrAnn) [(FST (HD ivenv), x)]))) ≤ getAnn trErrAnn
Proof
  rpt $ (disch_then strip_assume_tac ORELSE gen_tac)
  >> drule approxTransc_sound >> rpt $ disch_then drule
  >> disch_then $ qspec_then ‘[(FST (HD ivenv), x)]’ mp_tac
  >> impl_tac
  >- (
    gs[varsContained_def] >> Cases_on ‘ivenv’ >> gs[LENGTH]
    >> rpt VAR_EQ_TAC >> gs[FIND_def, INDEX_FIND_def]
    >> Cases_on ‘h’ >> gs[])
  >> disch_then strip_assume_tac >> gs[PULL_EXISTS, optionGet_def]
QED

val _ = export_theory();
