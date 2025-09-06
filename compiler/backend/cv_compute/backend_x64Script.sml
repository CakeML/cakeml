(*
  Define x64 specialised backend functions.
*)
Theory backend_x64
Ancestors
  x64_target
Libs
  preamble backend_asmLib


val _ = define_target_specific_backend x64_config_def;

