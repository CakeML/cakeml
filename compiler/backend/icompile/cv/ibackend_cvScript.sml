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
val arch_size = “:64”
val arch_spec = INST_TYPE [alpha |-> arch_size];
val _ = cv_auto_trans locationTheory.unknown_loc_def;
val asm_spec_mem_list = CONJUNCTS asm_spec_memory;
val (asm_spec, _) = asm_spec_raw asm_spec_mem_list x64_targetTheory.x64_config_def;
val asm_spec' = fn th => asm_spec th |> snd;

(* translating icompile_source_to_livesets *)
val _ = word0_to_livesets_def |> asm_spec' |> arch_spec |> cv_auto_trans;
val _ = icompile_bvl_to_bvi_prog_def
          |> SRULE [GSYM bvl_to_bviTheory.alloc_glob_count_eq_global_count_list]
          |> cv_auto_trans;
val _ = icompile_source_to_livesets_def |> asm_spec' |> cv_auto_trans;
(* no problem *)


(* tried translating each phases one by one, no problem *)
val _ = cv_auto_trans init_icompile_source_to_flat_def;
val _ = cv_auto_trans init_icompile_flat_to_clos_def;
val _ = cv_auto_trans init_icompile_clos_to_bvl_def;
val _ = cv_auto_trans init_icompile_bvl_to_bvi_def;
val _ = cv_auto_trans bvi_to_dataTheory.compile_prog_def;
val _ = init_icompile_data_to_word_def |> asm_spec' |> arch_spec |> cv_auto_trans;

(* then when i do this, then there is a problem *)
val _ = cv_auto_trans (icompile_data_to_word_def |> arch_spec);
val _ = init_icompile_source_to_livesets_def |> arch_spec |> asm_spec' |> cv_auto_trans; (* <----- problematic *)

(* translating end_icompile_source_to_livesets no problem *)
val _ = end_icompile_source_to_livesets_def |> asm_spec' |> cv_auto_trans;


(* constructing mconfig *)
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


(* replace with hello progs *)
val prog = ``REPLICATE 10 (ast$Dlet unknown_loc Pany (Con NONE []))``;


(* just in case i forget *)
(*Globals.max_print_depth := 20; *)

val init_res = cv_eval “init_icompile_to_livesets_x64 ^source_conf ^clos_conf ^bvl_conf ^data_conf ^word_conf”

(* init *)
val (source_iconf_lvs, rest) = pairSyntax.dest_pair (rconc init_res);
val (clos_iconf_lvs, rest) = pairSyntax.dest_pair rest;
val (bvl_iconf_lvs, rest) = pairSyntax.dest_pair rest;
val (data_conf_lvs, rest) = pairSyntax.dest_pair rest;
val (reg_count_and_lvs_data, livesets_init) = pairSyntax.dest_pair rest;
val (reg_count, lvs_data) = pairSyntax.dest_pair reg_count_and_lvs_data;

val source_iconf = ref source_iconf_lvs;
val clos_iconf = ref clos_iconf_lvs;
val bvl_iconf = ref bvl_iconf_lvs;
val lvs_data_acc : term list ref = ref [lvs_data];
val prog_acc = ref [livesets_init];
(*=======*)


(* public *)
fun icompile (prog : term) =
  let
   val res_opt = cv_eval “icompile_to_livesets_x64 ^(!source_iconf) ^(!clos_iconf) ^(!bvl_iconf) ^data_conf_lvs ^word_conf ^prog” |> rconc;
   val res = res_opt |> optionSyntax.dest_some;
   val (source_iconf', rest) = pairSyntax.dest_pair (res);
   val (clos_iconf', rest) = pairSyntax.dest_pair rest;
   val (bvl_iconf', rest) = pairSyntax.dest_pair rest;
   val (lvs_data', prog') = pairSyntax.dest_pair rest;
   val _ = source_iconf := source_iconf';
   val _ = clos_iconf := clos_iconf';
   val _ = bvl_iconf := bvl_iconf';
   val _ = lvs_data_acc := (lvs_data' :: (!lvs_data_acc));
   val _ = prog_acc := (prog' :: (!prog_acc))
  in ()

 end

(* public *)
fun end_icompile () =

  let
    val end_res =
        cv_eval “end_icompile_to_livesets_x64 ^(!source_iconf) ^source_conf
                                              ^(!clos_iconf) ^clos_conf
                                              ^(!bvl_iconf) ^bvl_conf
                                              ^data_conf_lvs ^word_conf”
          |> rconc;
   val (source_conf, rest) = pairSyntax.dest_pair end_res;
   val (clos_conf, rest) = pairSyntax.dest_pair rest;
   val (bvl_conf, rest) = pairSyntax.dest_pair rest;
   val (lvs_data_end, livesets_end) = pairSyntax.dest_pair rest;
   val _ = lvs_data_acc := (lvs_data_end :: !lvs_data_acc);
   val _ = prog_acc := (livesets_end :: !prog_acc);
  in
    (source_conf, clos_conf, bvl_conf, rev (!lvs_data_acc), rev (!prog_acc))
end



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

(* user interface *)
icompile prog;
val final_res = end_icompile ()

val _ = export_theory();
