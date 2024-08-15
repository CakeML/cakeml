(*
  Definitions used to trick EVAL in xcf.sml.
 *)

open preamble cfTheory;

val _ = new_theory "xcf";

Definition STOP_def:
  STOP x y = y
End

Theorem cf_STOP_thm:
  cf p x env H Q = cf p x (STOP STOP env) (STOP STOP H) (STOP STOP Q)
Proof
  rw [STOP_def]
QED

Theorem cf_STOP:
  cf p x = \env H Q. cf p x (STOP STOP env) (STOP STOP H) (STOP STOP Q)
Proof
  rw [STOP_def, FUN_EQ_THM]
QED

Theorem cf_STOP_rewrite =
  List.map
    (CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [cf_STOP])) o SPEC_ALL)
    (CONJUNCTS cf_def)
  |> LIST_CONJ;

val _ = export_theory ();

