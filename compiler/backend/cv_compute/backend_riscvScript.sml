(*
  Define riscv specialised backend functions.
*)

open preamble backend_asmLib riscv_targetTheory;

val _ = new_theory "backend_riscv";

val _ = define_target_specific_backend riscv_config_def;

val _ = export_theory();
