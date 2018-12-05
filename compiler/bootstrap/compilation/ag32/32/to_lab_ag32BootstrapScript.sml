(*
  Evaluate the 32-bit version of the compiler down to a LabLang
  program (an assembly program).
*)
open preamble
     backendTheory
     to_dataBootstrapTheory
     ag32_configTheory
     ag32_targetTheory
     ag32_targetLib asmLib

val _ = new_theory "to_lab_ag32Bootstrap";

val _ = Globals.max_print_depth := 10;

val new_clos_conf =
  (REWRITE_CONV [init_conf_def] THENC EVAL) ``init_conf.clos_conf`` |> concl |> rand

val bootstrap_conf =
  ``((ag32_backend_config
      with clos_conf := ^new_clos_conf)
     with
     bvl_conf updated_by
       (λc. c with <| inline_size_limit := 3; exp_cut := 200 |>))
     with
     data_conf updated_by
       (λc. c with <| call_empty_ffi := T (* enables logging messages *) |>)``

val to_data_thm0 =
  MATCH_MP backendTheory.to_data_change_config to_data_ag32_thm
  |> Q.GEN`c2` |> ISPEC bootstrap_conf

val same_config = prove(to_data_thm0 |> concl |> rator |> rand,
  REWRITE_TAC[init_conf_def,ag32_backend_config_def]
  \\ EVAL_TAC
  \\ rw[FLOOKUP_EXT,FUN_EQ_THM,FLOOKUP_UPDATE,FLOOKUP_FUNION]
  \\ EVAL_TAC
  \\ rpt (IF_CASES_TAC \\ rveq \\ EVAL_TAC))

val to_data_thm1 =
  MATCH_MP to_data_thm0 same_config

(*
val (ls,ty) = data_prog_ag32_def |> rconc |> listSyntax.dest_list
val data_prog_ag32' =  listSyntax.mk_list(List.take(ls,10),ty)
val data_prog_ag32_shorten = mk_thm([],``data_prog_ag32 = ^data_prog_ag32'``)
val to_data_thm1 = PURE_REWRITE_RULE[data_prog_ag32_shorten]to_data_thm1
val to_data_thm = to_data_thm1
*)

val stack_to_lab_thm = save_thm("stack_to_lab_thm",
  compilationLib.compile_to_lab data_prog_ag32_def to_data_thm1 "lab_prog");

val () = ml_translatorLib.reset_translation();

val () = export_theory();
