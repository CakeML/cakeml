(*
  Compiles the LSR checker by evaluation inside the logic of HOL
*)
Theory lsrCompile
Ancestors
  lsr_arrayFullProg x64_config
Libs
  preamble eval_cake_compile_x64Lib

(* The group walk takes 12 arguments and the round 11; with max_app at least
  that, every call to them is a full application *)
Definition x64_config'_def:
  x64_config' =
  x64_backend_config with
    clos_conf := x64_backend_config.clos_conf with max_app := 16
End

Theorem lsr_array_compiled =
  eval_cake_compile_x64_with_conf "" x64_config'_def check_unsat_prog_def
    "cake_lsr.S";
