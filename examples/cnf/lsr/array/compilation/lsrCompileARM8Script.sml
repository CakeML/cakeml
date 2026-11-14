(*
  Compiles the LSR checker for ARM8 by evaluation inside the logic of HOL
*)
Theory lsrCompileARM8
Ancestors
  lsr_arrayFullProg arm8_config
Libs
  preamble eval_cake_compile_arm8Lib

(* The group walk takes 12 arguments and the round 11; with max_app at least
  that, every call to them is a full application *)
Definition arm8_config'_def:
  arm8_config' =
  arm8_backend_config with
    clos_conf := arm8_backend_config.clos_conf with max_app := 16
End

Theorem lsr_array_compiled =
  eval_cake_compile_arm8_with_conf "" arm8_config'_def check_unsat_prog_def
    "cake_lsr_arm8.S";
