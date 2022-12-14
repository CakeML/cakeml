(**
  A simple checker for polynomial evaluation
  Part one of the soundness proof requires showing that the approximated
  polynomial agrees with what Remez thought the trancendental function behaves
  like on the set of points Ω

  Currently not used in Dandelion
**)

open realTheory realLib RealArith stringTheory;
open renameTheory realPolyTheory transcLangTheory checkerDefsTheory;
open preambleDandelion;

val _ = new_theory "pointChecker";

(*
(* TODO: Check for each xi in Omega that p(xi) - f(xi) = cert.eps *)

Definition pointCheckerHelper_def:
  pointCheckerHelper [] transc poly eps = Valid ∧
  pointCheckerHelper (x1::xs) transc poly eps =
    if (abs (evalPoly poly  x1 - transc x1) = eps)
    then  (pointCheckerHelper xs transc poly eps)
    else Invalid "Point discrepancy"
End

Definition pointChecker_def:
  pointChecker (cert:certificate): result =
  if (LENGTH cert.omega = 0) then Invalid "Empty set" else
  (pointCheckerHelper cert.omega (λ x. interp cert.transc x) cert.poly cert.eps)
End
*)

val _ = export_theory();
