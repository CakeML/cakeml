(*
  A pure version of the VIPR checker
*)
open preamble milpTheory;

val _ = new_theory "vipr_checker"

Datatype:
  reader_state = Init
               | ReadingProblem (mlstring list)
               | Error mlstring
End

Definition init_state_def:
  init_state = Init
End

Definition checker_step_def:
  checker_step (line:mlstring) (s:reader_state) = s
End

Definition print_outcome_def:
  print_outcome (s:reader_state) = strlit "TODO"
End

val _ = export_theory();
