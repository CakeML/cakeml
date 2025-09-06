(*
  Define ag32 specialised backend functions.
*)
Theory backend_ag32
Ancestors
  ag32_target
Libs
  preamble backend_asmLib


val _ = define_target_specific_backend ag32_config_def;

