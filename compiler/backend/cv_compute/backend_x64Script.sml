(*
  Define x64 specialised backend functions.
*)

open preamble backend_asmLib x64_targetTheory;

val _ = new_theory "backend_x64";

val memory = define_target_specific_backend x64_config_def;

val _ = save_thm("asm_spec_memory",memory)

val _ = export_theory();
