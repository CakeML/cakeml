(*
  testestestes
*)

open preamble;

val _ = new_theory "less_lemma";

Theorem less_add_1:
  ∀n. n < n + 1
Proof
  DECIDE_TAC
QED

val _ = export_theory();
