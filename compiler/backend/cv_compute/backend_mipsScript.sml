(*
  Define mips specialised backend functions.
*)

open preamble backend_asmLib mips_targetTheory;

val _ = new_theory "backend_mips";

val _ = define_target_specific_backend mips_config_def;

val _ = export_theory();
