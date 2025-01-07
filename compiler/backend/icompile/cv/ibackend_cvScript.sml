(*
  Quick test file for ibackend
*)
open preamble ibackendTheory
     backend_asmTheory
     backend_x64Theory
     to_data_cvTheory
     backend_64_cvTheory
     backend_x64_cvTheory
     cv_transLib
     x64_configTheory
     x64_targetTheory
;
open backend_asmLib;
open helloProgTheory;

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
val arch_size = “:64”
val arch_spec = INST_TYPE [alpha |-> arch_size];
(* Some basic setup *)
val _ = cv_auto_trans locationTheory.unknown_loc_def;
val _ = cv_auto_trans source_to_sourceTheory.compile_def;
val _ = cv_auto_trans init_icompile_source_to_flat_def;
val _ = cv_auto_trans init_icompile_flat_to_clos_def;
val _ = cv_auto_trans init_icompile_clos_to_bvl_def;
val eq = icompile_bvl_to_bvi_prog_def |> SRULE [GSYM bvl_to_bviTheory.alloc_glob_count_eq_global_count_list];
val _ = cv_auto_trans eq;
val _ = cv_auto_trans init_icompile_bvl_to_bvi_def;
val _ = cv_trans bvi_to_dataTheory.compile_prog_def;
val _ = cv_auto_trans icompile_source_to_flat_def;
val _ = cv_auto_trans icompile_flat_to_clos_def;
val eq = icompile_clos_to_bvl_prog_def |> SRULE [clos_to_bvlTheory.compile_exp_sing_eq]
val _ = cv_auto_trans eq
val _ = cv_auto_trans icompile_clos_to_bvl_def;
val _ = cv_auto_trans (icompile_data_to_word_def |> arch_spec);
val _ = cv_auto_trans end_icompile_source_to_flat_def;
val _ = cv_auto_trans end_icompile_clos_to_bvl_def;
val _ = cv_auto_trans end_icompile_bvl_to_bvi_def;

val c = x64_backend_config_def |> concl |> lhs;
val x64_ic_term = backendTheory.config_to_inc_config_def
       |> ISPEC c |> CONV_RULE (RAND_CONV EVAL) |> rconc;
val x64_c_term = EVAL c |> rconc;
val source_conf = EVAL ``^(c).source_conf with init_vidx := 1000`` |> rconc;
val clos_conf = EVAL ``^(c).clos_conf`` |> rconc;
val bvl_conf = EVAL ``^(c).bvl_conf`` |> rconc;
val data_conf = EVAL ``^(c).data_conf`` |> rconc;
val asm_conf = EVAL ``^(c).lab_conf.asm_conf`` |> rconc;
val word_conf = EVAL ``^(c).word_to_word_conf`` |> rconc;
val stack_conf = EVAL ``^(c).stack_conf`` |> rconc;

val prog = ``REPLICATE 10 (ast$Dlet unknown_loc Pany (Con NONE []))``;

(*
val res = cv_eval ``init_icompile_source_to_flat ^source_conf``;
val (source_iconf,flat_stub) = pairSyntax.dest_pair (rconc res);
val clos_stub = cv_eval “init_icompile_flat_to_clos ^flat_stub” |> rconc;
val res = cv_eval ``init_icompile_clos_to_bvl ^clos_conf ^clos_stub``;
val (clos_iconf, bvl_init) = pairSyntax.dest_pair (rconc res);

val res = cv_eval ``init_icompile_bvl_to_bvi ^bvl_conf ^bvl_init``;
val (bvl_iconf, bvi_init) = pairSyntax.dest_pair (rconc res);
val data_init = cv_eval ``bvi_to_data$compile_prog ^bvi_init`` |> rconc;
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
*)

(* livesets *)

val asm_spec_mem_list = CONJUNCTS asm_spec_memory;
val (asm_spec, _) = asm_spec_raw asm_spec_mem_list x64_targetTheory.x64_config_def;
val asm_spec' = fn th => asm_spec th |> snd

val _ = cv_auto_trans (asm_spec' init_icompile_data_to_word_def |> arch_spec)
val _ = cv_auto_trans (to_livesets_0_x64_def);
val _ = cv_auto_trans (icompile_data_to_word_def |> arch_spec)
val _ = cv_auto_trans (asm_spec' to_livesets_0_alt_def )
val _ = cv_auto_trans (asm_spec' icompile_to_livesets_def)
val _ = cv_auto_trans (asm_spec' init_icompile_to_livesets_def)
val _ = cv_auto_trans (asm_spec' end_icompile_to_livesets_def)

(* just in case i forget *)
(*Globals.max_print_depth := 20; *)

val init_res = cv_eval “init_icompile_to_livesets_x64 ^source_conf ^clos_conf ^bvl_conf ^data_conf ^word_conf”

val (source_iconf_lvs, rest) = pairSyntax.dest_pair (rconc init_res);
val (clos_iconf_lvs, rest) = pairSyntax.dest_pair rest;
val (bvl_iconf_lvs, rest) = pairSyntax.dest_pair rest;
val (data_conf_lvs, rest) = pairSyntax.dest_pair rest;
val (reg_count_and_lvs_data, livesets_init) = pairSyntax.dest_pair rest;
val (reg_count, lvs_data) = pairSyntax.dest_pair reg_count_and_lvs_data;

(* very slow *)
val res_opt = cv_eval “icompile_to_livesets_x64 ^source_iconf_lvs ^clos_iconf_lvs ^bvl_iconf_lvs ^data_conf_lvs ^word_conf ^prog []”

(* debug *)
val source_prog = cv_eval “source_to_source$compile ^prog” |> rconc;
val (source_iconf', flat_prog) = cv_eval “icompile_source_to_flat ^source_iconf_lvs ^prog” |> rconc |> optionSyntax.dest_some |> pairSyntax.dest_pair;
val clos_prog = cv_eval “icompile_flat_to_clos ^flat_prog” |> rconc;
val (clos_iconf', bvl_prog) = cv_eval “icompile_clos_to_bvl ^clos_iconf_lvs ^clos_prog” |> rconc |> pairSyntax.dest_pair;
val (bvl_iconf', bvi_prog) = cv_eval “icompile_bvl_to_bvi ^bvl_iconf_lvs ^bvl_prog” |> rconc |> pairSyntax.dest_pair;
val data_prog = cv_eval “bvi_to_data$compile_prog ^bvi_prog” |> rconc;
val word0_prog = cv_eval “(icompile_data_to_word ^data_conf_lvs ^data_prog) : (num # num # 64 wordLang$prog) list” |> rconc;
val (reg_count_and_lvs_data_prog, word_prog) = cv_eval “to_livesets_0_alt_x64 (^word_conf, ^word0_prog)” |> rconc |> pairSyntax.dest_pair;
val (reg_count_prog, lvs_data_prog) = pairSyntax.dest_pair reg_count_and_lvs_data_prog;


val end_res = cv_eval “end_icompile_to_livesets_x64 ^source_iconf' ^source_conf
                                                    ^clos_iconf' ^clos_conf
                                                    ^bvl_iconf' ^bvl_conf
                                                    ^data_conf_lvs ^word_conf”



val _ = export_theory();
