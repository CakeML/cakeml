(*
  CV translation for ibackend
*)
open preamble ibackendTheory
     backend_asmTheory
     backend_x64Theory
     to_data_cvTheory
     backend_64_cvTheory
     backend_x64_cvTheory
     cv_transLib
     x64_configTheory
     x64_targetTheory;

open backend_asmLib;
open helloProgTheory;

val _ = new_theory"ibackend_cv";

(* using the default config for x64 *)
val arch_size = “:64”
val arch_spec = INST_TYPE [alpha |-> arch_size];

val asm_spec_mem_list = CONJUNCTS asm_spec_memory;
val (asm_spec, _) = asm_spec_raw asm_spec_mem_list x64_targetTheory.x64_config_def;
val asm_spec' = fn th => asm_spec th |> snd;

val _ = cv_auto_trans locationTheory.unknown_loc_def;

(* translating icompile_source_to_livesets *)
(* val _ = to_word_0_alt_def |> asm_spec' |> arch_spec |> cv_auto_trans; *)
(* val _ = to_livesets_0_def |> asm_spec' |> cv_trans *)
val _ = to_livesets_0_alt_def |>
  SIMP_RULE std_ss [backendTheory.word_internal_def,
  LET_DEF |> INST_TYPE [alpha |-> ``:bool``]] |> asm_spec' |> cv_auto_trans;

val _ = cv_auto_trans
  (icompile_bvl_to_bvi_prog_def
  |> SRULE [GSYM bvl_to_bviTheory.alloc_glob_count_eq_global_count_list]);

val _ = end_icompile_source_to_livesets_def |> asm_spec' |> cv_auto_trans;

val _ = icompile_source_to_livesets_def |> asm_spec' |> cv_auto_trans;

val _ = init_icompile_data_to_word_def |> asm_spec' |> arch_spec |> cv_auto_trans ;

val _ = cv_trans empty_word_iconf_def;

val _ = mk_iconfig_def |> cv_auto_trans ;

val _ = init_icompile_source_to_livesets_def |> asm_spec' |> cv_auto_trans;


val c = x64_backend_config_def |> concl |> lhs;
val x64_inc_conf = backendTheory.config_to_inc_config_def
                     |> ISPEC c |> CONV_RULE (RAND_CONV EVAL) |> rconc;
val inc_source_conf_init_vidx = EVAL “^(x64_inc_conf).inc_source_conf with init_vidx := 10000” |> rconc;
val x64_inc_conf = EVAL “^(x64_inc_conf) with inc_source_conf := ^(inc_source_conf_init_vidx)” |> rconc;
val prog = hello_prog_def |> rconc;

(* init icompile *)
val init_res = time cv_eval “init_icompile_source_to_livesets_x64 ^(x64_inc_conf)” |> rconc;
val (ic, reg_count_and_data_and_prog) = pairSyntax.dest_pair init_res;
val (reg_count_and_data, prog_after_init_ic) = pairSyntax.dest_pair reg_count_and_data_and_prog;
val (reg_count, data) = pairSyntax.dest_pair reg_count_and_data;
(* # runtime: 51.2s,    gctime: 8.8s,     systime: 22.0s. *)

(* one round of icompile *)
val icompile_res_opt = time cv_eval “icompile_source_to_livesets_x64 ^ic ^prog” |> rconc;
val icompile_res = optionSyntax.dest_some icompile_res_opt;
val (ic', data_and_prog) = pairSyntax.dest_pair icompile_res;
val (data_after_ic, prog_after_ic) = pairSyntax.dest_pair data_and_prog;
(* # runtime: 5m38s,    gctime: 26.3s,     systime: 19.3s. *)

(* end icompile *)
val end_icompile_res = time cv_eval “end_icompile_source_to_livesets_x64 ^(ic') ^(x64_inc_conf)” |> rconc;
val (inc_conf_after_ic, data_and_prog_end_ic) = pairSyntax.dest_pair end_icompile_res;
val (data_after_end_ic, prog_after_end_ic) = pairSyntax.dest_pair data_and_prog_end_ic;
(*# runtime: 3m51s,    gctime: 25.7s,     systime: 1m14s. *)



val _ = export_theory();
