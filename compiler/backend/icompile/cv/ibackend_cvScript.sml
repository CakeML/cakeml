(*
  Quick test file for ibackend
*)
open preamble ibackendTheory
     backend_asmTheory
     backend_x64Theory
     to_data_cvTheory
     cv_transLib
     x64_configTheory;

val _ = new_theory"ibackend_cv";

(* using the default config for x64 *)

(*
 conv == term -> thm
*)
Definition fib_def:
  fib n a b =
    if n = 0n then (a:num)
    else if n = 1 then b
    else fib (n-1) b (a+b)
End

val res = cv_trans fib_def;

(* time EVAL ``fib 2000 1 1``; *)
(* time cv_eval ``fib 2000 1 1``; *)

(* Some basic setup *)
val _ = cv_auto_trans locationTheory.unknown_loc_def;

val c = x64_backend_config_def |> concl |> lhs;
val x64_ic_term = backendTheory.config_to_inc_config_def
       |> ISPEC c |> CONV_RULE (RAND_CONV EVAL) |> rconc;
val x64_c_term = EVAL c |> rconc;
val source_conf = EVAL ``^(c).source_conf with init_vidx := 1000`` |> rconc;
val clos_conf = EVAL ``^(c).clos_conf`` |> rconc;

val prog = ``REPLICATE 10 (ast$Dlet unknown_loc Pany (Con NONE []))``;

(* Example of cv_eval on base compiler *)
val res = cv_eval ``
  let p = source_to_source$compile ^prog in
  let (fc,p) = source_to_flat$compile ^source_conf p in
    flat_to_clos$compile_decs p
  ``;

val res = cv_auto_trans init_icompile_source_to_flat_def;

val res = cv_eval ``init_icompile_source_to_flat ^source_conf``;

val (source_iconf,flat_stub) = pairSyntax.dest_pair (rconc res);

val res = cv_auto_trans icompile_source_to_flat_def;

val res = cv_eval ``icompile_source_to_flat ^source_iconf ^prog``;

(* TODO: get everything up to data cv_translated and tested with cv_eval *)


val _ = export_theory();
