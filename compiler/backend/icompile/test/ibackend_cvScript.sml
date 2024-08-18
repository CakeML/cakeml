(*
  Quick test file for ibackend
*)
open preamble ibackendTheory
     backend_asmTheory
     backend_arm8Theory
     to_data_cvTheory
     cv_transLib
     arm8_configTheory;

val _ = new_theory"ibackend_cv";

(* using the default config for arm8 *)
val c = arm8_backend_config_def |> concl |> lhs;
val arm8_ic_term = backendTheory.config_to_inc_config_def
       |> ISPEC c |> CONV_RULE (RAND_CONV EVAL) |> rconc;
val arm8_c_term = EVAL c |> rconc;

val res = cv_eval ``source_to_source$compile []``

val res = cv_auto_trans init_icompile_def;

val sconf = EVAL ``^(c).source_conf`` |> rconc;

(* the output of init_icompile *)
val siconf = cv_eval ``init_icompile ^(sconf)`` |> rconc

val res = cv_auto_trans icompile_def;
val res = cv_eval ``icompile ^(siconf) []``

val _ = export_theory();
