(*
  Formalization of And-Inverter Graphs based on AIGER and the format introduced
  in "Introducing Certificates to the Hardware Model Checking Competition".
*)

Theory aig
Ancestors
  list
  alist
  sorting

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

Definition is_true_def:
  (is_true (SOME T) = T) ∧
  (is_true _ = F)
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

(* TODO Pass circuit directly if get_{L,R,F} are only used on circuits. *)
Definition get_L_def:
  get_L (LRF: ('id # ('id # 'id)) list) = MAP FST LRF
End

Definition get_R_def:
  get_R (LRF: ('id # ('id # 'id)) list) = MAP (FST ∘ SND) LRF
End

Definition get_F_def:
  get_F (LRF: ('id # ('id # 'id)) list) = MAP (SND ∘ SND) LRF
End

Definition evaluate_circuit_def:
  evaluate_circuit M ins s out =
  let input_ids = M.I in
  let latch_ids = get_L M.LRF in
  let circuit_ins = ZIP (input_ids, ins) ++ ZIP (latch_ids, s) in
    evaluate circuit_ins M.G (Pos out)
End

Definition is_reset_def:
  is_reset M s =
  let latch_ids = get_L M.LRF in
  let latch_lits = MAP Pos latch_ids in
  let is_reset_latches = MAP (evaluate (ZIP (latch_ids, s)) M.G) latch_lits in
    is_true (FOLDR tri_and (SOME T) is_reset_latches)
End

Definition is_step_def:
  is_step M ins curs nexts =
    LIST_REL (λout next. evaluate_circuit M ins curs out = next)
      (get_F M.LRF) nexts
End

Definition unsafe_def:
  unsafe M n ⇔
    ∃(inputs: value list) (trace: (value list) list).
      (* A trace of length n is sequence of n + 1 states. *)
      LENGTH trace = n + 1 ∧
      (* A state holds the value of each latch *)
      EVERY (λs. LENGTH s = LENGTH M.LRF) trace ∧
      (* First state satisfies R *)
      is_reset M (HD trace) ∧
      (* Every pair of consecutive states satisfies F *)
      SORTED (is_step M inputs) trace ∧
      (* All states satisfy the constraint C *)
      EVERY (λs. is_true (evaluate_circuit M inputs s M.C)) trace ∧
      (* Last state violates P *)
      ¬is_true (evaluate_circuit M inputs (LAST trace) M.P)
End

Definition safe_def:
  safe M n = ¬unsafe M n
End

Definition valid_witness_def:
  valid_witness M M' n = T
End

(* Theorem 1 (from [2]) *)
Theorem valid_witness_imp_safe:
  valid_witness M M' n ⇒ safe M n
Proof
  cheat
QED

(* References

   [1] The AIGER And-Inverter Graph (AIG) Format Version 20071012
   [2] Introducing Certificates to the Hardware Model Checking Competition
 *)
