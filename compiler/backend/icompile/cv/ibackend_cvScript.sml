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
val bvl_conf = EVAL ``^(c).bvl_conf`` |> rconc;

val prog = ``REPLICATE 10 (ast$Dlet unknown_loc Pany (Con NONE []))``;

(* Example of cv_eval on base compiler *)
val res = cv_eval ``
  let p = source_to_source$compile ^prog in
  let (fc,p) = source_to_flat$compile ^source_conf p in
    flat_to_clos$compile_decs p
  ``;


val _ = cv_auto_trans source_to_sourceTheory.compile_def;
  
val _ = cv_auto_trans init_icompile_source_to_flat_def;

val res = cv_eval ``init_icompile_source_to_flat ^source_conf``;    

val (source_iconf,flat_stub) = pairSyntax.dest_pair (rconc res);

val _ = cv_auto_trans init_icompile_flat_to_clos_def;

val clos_stub = cv_eval “init_icompile_flat_to_clos ^flat_stub” |> rconc; 

val _ = cv_auto_trans init_icompile_clos_to_bvl_def;

val res = cv_eval ``init_icompile_clos_to_bvl ^clos_conf ^clos_stub``;
    
val (clos_iconf, bvl_init) = pairSyntax.dest_pair (rconc res);  

val eq = icompile_bvl_to_bvi_prog_def |> SRULE [GSYM bvl_to_bviTheory.alloc_glob_count_eq_global_count_list];

val _ = cv_auto_trans eq;    
    
val _ = cv_auto_trans init_icompile_bvl_to_bvi_def; 

val res = cv_eval ``init_icompile_bvl_to_bvi ^bvl_conf ^bvl_init``;

val (bvl_iconf, bvi_init) = pairSyntax.dest_pair (rconc res);                      

val _ = cv_trans bvi_to_dataTheory.compile_prog_def;

val data_init = cv_eval ``bvi_to_data$compile_prog ^bvi_init`` |> rconc; 

(* icompile *)

val _ = cv_auto_trans icompile_source_to_flat_def;
val _ = cv_auto_trans icompile_flat_to_clos_def;
val icompiled_to_data_opt = cv_eval “
  let p = source_to_source$compile ^prog in
    case icompile_source_to_flat ^source_iconf p of NONE => NONE
    | SOME (source_iconf', icompiled_p_flat) =>
        let icompiled_p_clos = icompile_flat_to_clos icompiled_p_flat in
        let (clos_iconf', icompiled_p_bvl) = icompile_clos_to_bvl_alt ^clos_iconf icompiled_p_clos in
        let (bvl_iconf', icompiled_p_bvi) = icompile_bvl_to_bvi ^bvl_iconf icompiled_p_bvl in
        let icompiled_p_data = bvi_to_data$compile_prog icompiled_p_bvi in
          SOME (source_iconf', clos_iconf', bvl_iconf', icompiled_p_data)
          ” |> rconc;

val _ = cv_auto_trans end_icompile_source_to_flat_def;
val _ = cv_auto_trans end_icompile_clos_to_bvl_def;
val _ = cv_auto_trans end_icompile_bvl_to_bvi_def;

val res = cv_eval “
 case ^icompiled_to_data_opt of NONE => NONE |
 SOME (source_iconf, clos_iconf, bvl_iconf, icompiled_p_data) =>
               let source_conf_after_ic = end_icompile_source_to_flat source_iconf ^source_conf in
               let (clos_conf_after_ic, bvl_end) = end_icompile_clos_to_bvl clos_iconf ^clos_conf in
               let (clos_conf_after_ic_bvi, bvl_conf_after_ic, bvi_end) =
                   end_icompile_bvl_to_bvi bvl_end bvl_iconf clos_conf_after_ic ^bvl_conf in
               let data_end = bvi_to_data$compile_prog bvi_end in
                 SOME (source_conf_after_ic, clos_conf_after_ic_bvi, bvl_conf_after_ic, ^data_init ++ icompiled_p_data ++ data_end)
”;


val _ = export_theory();
