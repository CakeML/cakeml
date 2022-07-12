(**
  Connection to FloVer roundoff error analyzer, currently unused
**)

open ExpressionsTheory ExpressionSemanticsTheory realPolyTheory
open preambleDandelion;

val _ = new_theory "floverConn";

Definition poly2FloVer_def:
  poly2FloVer []:real expr = Const REAL 0 ∧
  poly2FloVer (c1::cs) = Binop Plus (Const REAL c1) (Binop Mult (Var 0) (poly2FloVer cs))
End

Theorem polyEval_implies_FloVer_eval:
  ∀ (p:poly) (x:real) (r:real).
    evalPoly p x = r ⇒
    eval_expr (λ v:num. if v = 0 then SOME x else NONE) (λ e:real expr. SOME REAL) (poly2FloVer p) r REAL
Proof
  Induct_on ‘p’ >> gs[evalPoly_def, eval_expr_rules, poly2FloVer_def]
  >> rpt strip_tac
  >- (
    irule Const_dist' >> gs[]
    >> qexists_tac ‘0’ >> gs[perturb_def, MachineTypeTheory.mTypeToR_pos])
  >> irule Binop_dist'
  >> qexists_tac ‘0’ >> gs[perturb_def, MachineTypeTheory.mTypeToR_pos, MachineTypeTheory.isJoin_def]
  >> ntac 2 $ qexists_tac ‘REAL’
  >> qexists_tac ‘h’ >> qexists_tac ‘x * evalPoly p x’
  >> gs[evalBinop_def, MachineTypeTheory.isFixedPoint_def, MachineTypeTheory.join_fl_def]
  >> conj_tac
  >- (
    irule Const_dist' >> gs[]
    >> qexists_tac ‘0’ >> gs[perturb_def, MachineTypeTheory.mTypeToR_pos])
  >> irule Binop_dist'
  >> qexists_tac ‘0’ >> gs[perturb_def, MachineTypeTheory.mTypeToR_pos, MachineTypeTheory.isJoin_def]
  >> ntac 2 $ qexists_tac ‘REAL’
  >> qexists_tac ‘x’ >> qexists_tac ‘evalPoly p x’
  >> gs[evalBinop_def, MachineTypeTheory.isFixedPoint_def, MachineTypeTheory.join_fl_def]
  >> irule Var_load >> gs[]
QED

Theorem FloVer_eval_real_typed:
  ∀ p r x m.
    eval_expr (λ v:num. if v = 0 then SOME x else NONE) (λ e. SOME REAL) (poly2FloVer p) r m ⇒
    m = REAL
Proof
  Induct_on `p` \\ rpt strip_tac \\ gs[poly2FloVer_def, Once eval_expr_cases]
QED

Theorem FloVer_eval_implies_polyEval:
  ∀ p x r.
    eval_expr (λ v:num. if v = 0 then SOME x else NONE) (λ e. SOME REAL) (poly2FloVer p) r REAL ⇒
    evalPoly p x = r
Proof
  Induct_on ‘p’ >> gs[evalPoly_def, eval_expr_cases, poly2FloVer_def]
  >> rpt strip_tac
  >- gs[perturb_def]
  >> qpat_x_assum `r = _` $ gs o single
  >> gs[perturb_def]
  >> imp_res_tac FloVer_eval_real_typed >> gs[]
  >> res_tac >> gs[evalBinop_def]
QED

Theorem evalPoly_Flover_eval_bisim:
  ∀ p x r.
    evalPoly p x = r ⇔
    eval_expr (λ v:num. if v = 0 then SOME x else NONE) (λ e. SOME REAL) (poly2FloVer p) r REAL
Proof
  rpt strip_tac >> EQ_TAC >> gs[FloVer_eval_implies_polyEval, polyEval_implies_FloVer_eval]
QED

val _ = export_theory();
