(*
  Define riscv specialised backend functions.
*)
Theory backend_riscv
Ancestors
  riscv_target
Libs
  preamble backend_asmLib


val _ = define_target_specific_backend riscv_config_def;

