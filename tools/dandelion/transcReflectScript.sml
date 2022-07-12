(**
  Simple reflection function translating elements of the deeply
  embedded transc datatype into the polynomials defined in
  realPolyScript.sml
**)
open realPolyTheory realPolyProofsTheory transcLangTheory;
open preambleDandelion;

val _ = new_theory"transcReflect";

Definition reflectToPoly_def:
  reflectToPoly (Var x) y = (if x = y then SOME (var 1) else NONE) ∧
  reflectToPoly (Cst c) y = SOME (cst c) ∧
  reflectToPoly (Uop u e) y =
    (case reflectToPoly e y of
    | NONE => NONE
    | SOME p =>
      if u ≠ Inv then SOME (poly_neg p)
      else NONE)
  ∧
  reflectToPoly (Bop b e1 e2) y =
    (case reflectToPoly e1 y of
    | NONE => NONE
    | SOME p1 =>
      case reflectToPoly e2 y of
      | NONE => NONE
      | SOME p2 =>
        if b ≠ Div then
          (case b of
           | Add => SOME (poly_add p1 p2)
           | Sub => SOME (poly_sub p1 p2)
           | Mul => SOME (poly_mul p1 p2))
        else NONE)
  ∧
  reflectToPoly (Poly p e) y =
    (case reflectToPoly e y of
    | NONE => NONE
    | SOME p1 => SOME (compose p p1))
  ∧
  reflectToPoly (Fun _ _) _ = NONE
End

Theorem reflectSemEq:
  ∀ tr p x xv v.
    reflectToPoly tr x = SOME p ∧
    interp tr [(x,xv)] = SOME v ⇒
    polyEvalsTo p xv v
Proof
  Induct_on ‘tr’ >> gs[reflectToPoly_def, interp_def, polyEvalsTo_def, CaseEq"option"]
  >> rpt strip_tac
  >- (
    first_x_assum $ drule_then drule
    >> rpt strip_tac >> rpt VAR_EQ_TAC
    >> gs[compose_correct])
  >- (
    ntac 2 $ last_x_assum $ drule_then drule
    >> rpt strip_tac >> rpt VAR_EQ_TAC
    >> Cases_on ‘b’ >> gs[] >> rpt VAR_EQ_TAC
    >> gs[appBop_def, eval_simps])
  >- (
    last_x_assum $ drule_then drule
    >> rpt strip_tac >> rpt VAR_EQ_TAC
    >> Cases_on ‘u’ >> gs[appUop_def, eval_simps])
  >- (
    gs[cst_def] >> IF_CASES_TAC
    >> gs[evalPoly_def])
  >> ‘1 = SUC 0’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> gs[var_def, evalPoly_def, FIND_def, INDEX_FIND_def]
  >> rpt VAR_EQ_TAC >> gs[]
QED

Theorem reflectSemEquiv:
  reflectToPoly tr x = SOME p ⇒
  interp tr [(x, xv)] = SOME (evalPoly p xv)
Proof
  reverse $ Cases_on ‘interp tr [(x, xv)]’ >> rpt strip_tac >> gs[]
  >- (
    drule reflectSemEq >> disch_then drule
    >> gs[polyEvalsTo_def])
  >> rpt $ pop_assum mp_tac
  >> SPEC_TAC (“p:real list”, “p:real list”)
  >> Induct_on ‘tr’ >> gs[interp_def, reflectToPoly_def]
  >> rpt strip_tac >> res_tac >> gs[FIND_def, INDEX_FIND_def, CaseEq"option"]
QED

val _ = export_theory();
