(*
  Define arm8 specialised backend functions.
*)
Theory backend_arm8
Ancestors
  arm8_target
Libs
  preamble backend_asmLib


val _ = define_target_specific_backend arm8_config_def;

