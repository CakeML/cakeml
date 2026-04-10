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

(* spo = strict partial order *)
Theorem stratification_reset_exists:
  is_stratified reset spo circ is ⇒ ∃s. is_reset sis circ reset
Proof
  cheat
QED
