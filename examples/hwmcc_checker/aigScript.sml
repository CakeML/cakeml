(*
  Formalization of And-Inverter Graphs based on AIGER and the format introduced
  in "Introducing Certificates to the Hardware Model Checking Competition".
*)

Theory aig
Ancestors
  alist

(* Three-valued logic as defined in Section 14 of [1]. *)
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

(* output, inputs to and gate *)
Type gate = “:('id # ('id literal # 'id literal))”

(* Note that in the base semantics
   - gates are treated as if they were topologically sorted.
   - "shadowing" of gates (different gates with the same id) is possible.
   - references to undeclared ids are considered equivalent to uninitialized.
   - latches are not considered separately; instead, they are just another input
     to the circuit. *)
Definition evaluate_def:
  (evaluate ins [] out =
    let id = get_id out in
    case ALOOKUP ins id of
    | SOME v => if is_pos out then v else tri_not v
    | NONE => NONE) ∧
  (evaluate ins ((g_out, (g_in₁, g_in₂))::rest) out =
    if g_out ≠ get_id out then
      evaluate ins rest out
    else
      let g_in₁ = evaluate ins rest g_in₁ in
      let g_in₂ = evaluate ins rest g_in₂ in
      let v = tri_and g_in₁ g_in₂ in
        if is_pos out then v else tri_not v)
End

(* [2] define circuits as a tuple M = (I, L, R, F, P, C), where R, F, P and C
   are predicates. In AIGER, these are simply outputs of a multi-rooted
   And-Inverter Graph, which we represent with G. Thus, we can represent R, F, P
   and C as 'id.  Additionally, since there is a reset state and transition for
   each latch, we collapse L, R, and F into one object LRF. *)
Datatype:
  circuit = <|
    G : ('id gate) list;  (* defines all predicates *)
    I : 'id list;  (* inputs *)
    LRF : ('id # ('id # 'id)) list;  (* (latch, (reset, transition)) *)
    P : 'id;  (* defines good states *)
    C : 'id;  (* defines set of states valid under it constraint *)
  |>
End

Definition valid_circuit_def:
  valid_circuit = T
End

Definition unsafe_def:
  unsafe M = T
End

Definition safe_def:
  safe M = ¬unsafe M
End

Definition valid_witness_def:
  valid_witness M M' = T
End

(* Theorem 1 (from [2]) *)
Theorem valid_witness_imp_safe:
  valid_witness M M' ⇒ safe M
Proof
  cheat
QED

(* References

   [1] The AIGER And-Inverter Graph (AIG) Format Version 20071012
   [2] Introducing Certificates to the Hardware Model Checking Competition
 *)
