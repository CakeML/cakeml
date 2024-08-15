(*
  Define arm8 specialised backend functions.
*)

open preamble backend_asmLib arm8_targetTheory;

val _ = new_theory "backend_arm8";

val _ = define_target_specific_backend arm8_config_def;

val _ = export_theory();
