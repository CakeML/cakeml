open preamble;
open TypeSystemTheory TypeSoundInvariantsTheory;

val _ = new_theory "logRel";

(*
val _ = Hol_datatype `
world = <| index : num; Sigma1 : tenvS; Sigma2 : tenvS; omega : unit |>`;

val equiv_v_def = Define `
(equiv_v (Tvar_db n) (tenv:tenvE) (w:world) (v1:v) (v2:v) =
  ARB) ∧
(equiv_v (Tapp TC_int []) tenv w v1 v2 =
  (v1 = v2) ∧ 
  type_v 0 emp emp w.Sigma1 v1 (Tapp TC_int []) ∧
  type_v 0 emp emp w.Sigma2 v2 (Tapp TC_int [])) ∧
(equiv_v (Tapp TC_bool []) tenv w v1 v2 =
  (v1 = v2) ∧ 
  type_v 0 emp emp w.Sigma1 v1 (Tapp TC_bool []) ∧
  type_v 0 emp emp w.Sigma2 v2 (Tapp TC_bool [])) ∧
(equiv_v (Tapp TC_unit []) tenv w v1 v2 =
  (v1 = v2) ∧ 
  type_v 0 emp emp w.Sigma1 v1 (Tapp TC_unit []) ∧
  type_v 0 emp emp w.Sigma2 v2 (Tapp TC_unit [])) ∧
(equiv_v (Tapp TC_tup ts) tenv w v1 v2 =
*)

val _ = export_theory();
