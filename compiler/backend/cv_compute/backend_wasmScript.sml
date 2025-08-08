(*
  Define WASM specialised backend functions.
*)

open preamble backend_asmLib wasm_configTheory;

val _ = new_theory "backend_wasm";

val _ = define_target_specific_backend wasm_config_def;

val _ = export_theory();
