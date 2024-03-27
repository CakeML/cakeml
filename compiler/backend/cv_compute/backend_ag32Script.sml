(*
  Define ag32 specialised backend functions.
*)

open preamble backend_asmLib ag32_targetTheory;

val _ = new_theory "backend_ag32";

val _ = define_target_specific_backend ag32_config_def;

val _ = export_theory();
