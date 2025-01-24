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

open reg_allocComputeLib;

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
(*
(* init icompile *)
val init_res = time cv_eval “init_icompile_source_to_livesets_x64 ^(x64_inc_conf)” |> rconc;
val (ic, reg_count_and_data_and_prog) = pairSyntax.dest_pair init_res;
val (reg_count_and_data, prog_after_init_ic) = pairSyntax.dest_pair reg_count_and_data_and_prog;
val (reg_count, data_after_init_ic) = pairSyntax.dest_pair reg_count_and_data;
(* # runtime: 51.2s,    gctime: 8.8s,     systime: 22.0s. *)

(*
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
*)


val (dest_prog, dest_prog_type) = listSyntax.dest_list prog;

fun div_lst_into_n [] n = []
  | div_lst_into_n xs n =
    let val size = length xs div n in
    if size <= 1 then [xs]
    else
      let
          val (res, rest) = List.take (xs, size) |> (fn taken => (taken, List.drop (xs, size)))
        in
          res :: div_lst_into_n rest (n - 1)
        end
    end

val hol_type_for_lvs_data = type_of data_after_init_ic;
val hol_type_for_lvs_prog = type_of prog_after_init_ic;

(* bench mark for dividing prog into 2 parts, unsafe opening of option *)
fun fold_icompile ic [] = ()
  | fold_icompile ic (p :: ps) =
    let
      val res_opt = cv_eval “icompile_source_to_livesets_x64 ^ic ^p” |> rconc;
      val res = optionSyntax.dest_some res_opt;
      val (ic', data_and_prog) = pairSyntax.dest_pair res;
    in
      fold_icompile ic' ps
    end


val prog2parts = div_lst_into_n dest_prog 2 |> map (fn ts => listSyntax.mk_list (ts, dest_prog_type))
fun run2parts () = fold_icompile ic prog2parts;
time run2parts ();
(* # runtime: 6m12s,    gctime: 31.2s,     systime: 7.2s. *)

val prog3parts = div_lst_into_n dest_prog 3 |> map (fn ts => listSyntax.mk_list (ts, dest_prog_type));
fun run3parts () = fold_icompile ic prog3parts;
time run3parts ();
(* # runtime: 6m26s,    gctime: 30.0s,     systime: 9.7s. *)


*)
(*
val x = (fetch "-" "to_livesets_alt_x64_def") |> GEN_ALL
    |> SPEC (hello_prog_def |> concl |> lhs)
    |> SPEC (x64_inc_conf) |> concl |> lhs;
reg_allocComputeLib.get_oracle_raw reg_alloc.Irc (cv_eval_raw x |> rconc)
*)

(*
val init_data_raw = time cv_eval_raw “FST (SND (init_icompile_source_to_livesets_x64 ^(x64_inc_conf)))” |> rconc;

val oracles = reg_allocComputeLib.get_oracle_raw reg_alloc.Irc init_data_raw;

val c_oracle_tm = backendTheory.inc_set_oracle_def
                    |> SPEC (x64_inc_conf) |> SPEC oracles;
*)


val _ = export_theory();
