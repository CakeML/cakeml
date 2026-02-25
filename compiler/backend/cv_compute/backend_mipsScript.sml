(*
  Define mips specialised backend functions.
*)
Theory backend_mips
Ancestors
  mips_target
Libs
  preamble backend_asmLib


val _ = define_target_specific_backend mips_config_def;

