(**
  Soundness theorem of the point-wise equivalence checker
  Currently unused
**)
open realTheory realLib RealArith stringTheory;
open renameTheory realPolyTheory checkerDefsTheory pointCheckerTheory;
open realPolyProofsTheory;
open preambleDandelion;

val _ = new_theory "pointCheckerProofs";

(*
Theorem pointChecker_intermed:
  ∀ omega transc poly eps.
    pointCheckerHelper omega transc poly eps = Valid ⇒
    ∀xi.
      MEM xi omega ⇒
      abs (evalPoly poly xi − transc xi) = eps

Proof
  Induct_on ‘omega’
  >> gs[pointCheckerHelper_def]
  >> rpt strip_tac
  >> every_case_tac >> gs[]
QED

Theorem pointCheckerSound:
  ∀ (cert:certificate).
    pointChecker cert = Valid ⇒
      ∀ xi.
        MEM xi cert.omega ⇒
        abs ((evalPoly cert.poly xi) - (λ x. interp cert.transc x) xi) = cert.eps
Proof
 gs[pointChecker_def]
 >> rpt gen_tac >> cond_cases_tac >> gs[]
 >> rpt strip_tac
 >> drule pointChecker_intermed
 >> rpt $ disch_then drule >> gs[]
QED
*)

val _ = export_theory();
