(*
  Define arm7 specialised backend functions.
*)

open preamble backend_asmLib arm7_targetTheory;

val _ = new_theory "backend_arm7";

val _ = define_target_specific_backend arm7_config_def;

val _ = export_theory();
