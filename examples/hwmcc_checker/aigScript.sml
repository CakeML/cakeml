(*
  Formalization of And-Inverter Graphs
*)

Theory aig
Ancestors
  misc
Libs
  preamble

Datatype:
  gate = And ('a # bool) ('a # bool) | Latch 'l | Input 'i | Const bool
End

Type state = “:'l -> bool”
Type inputs = “:'i -> bool”
Type circuit[pp] = “:('a, ('a, 'l, 'i) gate) alist”

Definition eval_circuit_def:
  eval_circuit (s: 'l state, is: 'i inputs) (circ: ('a, 'l, 'i) circuit) (out: 'a) =
  case circ of
  | [] => F
  | (a, g)::rest =>
      if a = out then
       (case g of
        | Const b => b
        | Latch l => s l
        | Input i => is i
        | And (g₁, b₁) (g₂, b₂) =>
            (b₁ ⇔ eval_circuit (s, is) rest g₁) ∧
            (b₂ ⇔ eval_circuit (s, is) rest g₂))
      else eval_circuit (s, is) rest out
End

Definition next_state_def:
  next_state sis (circ: ('a, 'l, 'i) circuit) (next: 'l -> 'a) =
  eval_circuit sis circ ∘ next
End

Definition is_reset_def:
  is_reset sis (circ: ('a, 'l, 'i) circuit) (reset: 'l -> 'a) =
  ∀l. eval_circuit sis circ (reset l)
End

Definition preds_hold_def:
  preds_hold sis (circ: ('a, 'l, 'i) circuit) (xs: 'a set) =
  ∀x. x ∈ xs ⇒ eval_circuit sis circ x
End

Definition is_trace_def:
  is_trace (circ: ('a, 'l, 'i) circuit) (reset: 'l -> 'a) (next: 'l -> 'a)
    (cnstr: 'a set) (tr: num -> 'l state # 'i inputs)
  ⇔
    (∃is. let (s, _) = tr 0 in is_reset (s, is) circ reset) ∧
    ∀i.
      let (s, _) = tr (i + 1) in
      next_state (tr i) circ next = s ∧
      preds_hold (tr i) circ cnstr
End

Definition is_safe_def:
  is_safe (circ: ('a, 'l, 'i) circuit) (reset: 'l -> 'a) (next: 'l -> 'a)
    (cnstr: 'a set) (safe: 'a set) ⇔
    ∀tr.
      is_trace circ reset next cnstr tr ⇒ ∀i. preds_hold (tr i) circ safe
End

(* Place and-gates into separate namespace - used when merging witness and
   model circuits. *)
Definition leftify_and_def:
  (leftify_and (And (a₁, b₁) (a₂, b₂)) = And (INL a₁, b₁) (INL a₂, b₂)) ∧
  (leftify_and (Latch l) = Latch l) ∧
  (leftify_and (Input i) = Input i) ∧
  (leftify_and (Const b) = Const b)
End

Definition rightify_and_def:
  (rightify_and (And (a₁, b₁) (a₂, b₂)) = And (INR a₁, b₁) (INR a₂, b₂)) ∧
  (rightify_and (Latch l) = Latch l) ∧
  (rightify_and (Input i) = Input i) ∧
  (rightify_and (Const b) = Const b)
End

Definition leftify_and_entry_def:
  leftify_and_entry (a, g) = (INL a, leftify_and g)
End

Definition rightify_and_entry_def:
  rightify_and_entry (a, g) = (INR a, rightify_and g)
End

(* Place all gates into separate namespace - used when combining independent
   circuits, such as copies of the same circuit to represent different
   time steps. *)
Definition leftify_gate_def:
  (leftify_gate (And (a₁, b₁) (a₂, b₂)) = And (INL a₁, b₁) (INL a₂, b₂)) ∧
  (leftify_gate (Latch l) = Latch (INL l)) ∧
  (leftify_gate (Input i) = Input (INL i)) ∧
  (leftify_gate (Const b) = Const b)
End

Definition rightify_gate_def:
  (rightify_gate (And (a₁, b₁) (a₂, b₂)) = And (INR a₁, b₁) (INR a₂, b₂)) ∧
  (rightify_gate (Latch l) = Latch (INR l)) ∧
  (rightify_gate (Input i) = Input (INR i)) ∧
  (rightify_gate (Const b) = Const b)
End

Definition leftify_gate_entry_def:
  leftify_gate_entry (a, g) = (INL a, leftify_gate g)
End

Definition rightify_gate_entry_def:
  rightify_gate_entry (a, g) = (INR a, rightify_gate g)
End

(* "Merges" two circuits by having them share inputs and latches.

   This function assumes that the latches and inputs of left are a superset
   of those of right. If we consider the left circuit to be the witness, it is
   probably possible to have a preprocessing step that adjusts the witness
   latches and inputs to look something like this:

   ┌──────┬────────────────────────────────────┬────────────┐
   │shared│model-only (dummy/unused in witness)│witness-only│
   └──────┴────────────────────────────────────┴────────────┘
   ▲
   start
 *)
Definition merge_circuits_def:
  merge_circuits
    (left: ('a₁, 'l₁, 'i₁) circuit) (right: ('a₂, 'l₁, 'i₁) circuit) =
  MAP leftify_and_entry left ++ MAP rightify_and_entry right
End

(* Pairs two circuits by keeping gates, inputs and latches separate. *)
Definition pair_circuits_def:
  pair_circuits
    (left: ('a₁, 'l₁, 'i₁) circuit) (right: ('a₂, 'l₂, 'i₂) circuit) =
  MAP leftify_gate_entry left ++ MAP rightify_gate_entry right
End

Definition pair_reset_def:
  pair_reset (left_reset: 'l₁ -> 'a₁) (right_reset: 'l₂ -> 'a₂) l =
  case l of
  | INL l₁ => INL (left_reset l₁)
  | INR l₂ => INR (right_reset l₂)
End

(* spo = strict partial order *)
Theorem stratification_reset_exists:
  is_stratified reset spo circ is ⇒ ∃s. is_reset sis circ reset
Proof
  cheat
QED
