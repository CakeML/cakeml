(*
  Define arm7 specialised backend functions.
*)
Theory backend_arm7
Ancestors
  arm7_target
Libs
  preamble backend_asmLib


val _ = define_target_specific_backend arm7_config_def;

