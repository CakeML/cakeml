(*
  Formalization of And-Inverter Graphs based on AIGER and the format introduced
  in "Introducing Certificates to the Hardware Model Checking Competition".
*)

Theory aig
Ancestors
  alist

(* Three-valued logic as defined in Section 14 of
   "The AIGER And-Inverter Graph (AIG) Format Version 20071012". *)
Type value = “:bool option”

Definition tri_not_def:
  (tri_not (SOME b) = SOME ¬b) ∧
  (tri_not NONE = NONE)
End

Definition tri_and_def:
  (tri_and (SOME b₁) (SOME b₂) = SOME (b₁ ∧ b₂)) ∧
  (tri_and (SOME b) NONE = if ¬b then (SOME F) else NONE) ∧
  (tri_and NONE (SOME b) = if ¬b then (SOME F) else NONE) ∧
  (tri_and NONE NONE = NONE)
End

(* Since we do not need to settle on a specific type for id, we use a type
   variable. *)
Datatype:
  literal = Pos 'id | Neg 'id
End

Definition get_id_def:
  (get_id (Pos id) = id) ∧
  (get_id (Neg id) = id)
End

Definition is_pos_def:
  (is_pos (Pos id) = T) ∧
  (is_pos _ = F)
End

Type input = “:('id # value)”

(* output, inputs to and gate *)
Type gate = “:('id # ('id literal # 'id literal))”

(* output, current value, next state *)
Type latch = “:(('id # value) # ('id literal))”

(* Note that the semantics treats gates as if they were topologically sorted.
   Additionally, "shadowing" of gates (different gates with the same id) is
   possible.
   References to undeclared ids are considered equivalent to uninitialized. *)
Definition evaluate_def:
  (evaluate ins latches [] out =
    let id = get_id out in
    case ALOOKUP (MAP FST latches ++ ins) id of
    | SOME v => if is_pos out then v else tri_not v
    | NONE => NONE) ∧
  (evaluate ins latches ((g_out, (g_in₁, g_in₂))::rest) out =
    if g_out ≠ get_id out then
      evaluate ins latches rest out
    else
      let g_in₁ = evaluate ins latches rest g_in₁ in
      let g_in₂ = evaluate ins latches rest g_in₂ in
      let v = tri_and g_in₁ g_in₂ in
        if is_pos out then v else tri_not v)
End

Definition update_latches_def:
  update_latches ins latches gates =
    let (cur, next) = UNZIP latches in
    let (out, cur_vs) = UNZIP cur in
    let next_vs = MAP (evaluate ins latches gates) next in
      ZIP (ZIP (out, next_vs), next)
End
