(*
  icompile basis
*)

open preamble
     eval_cake_icompile_x64Lib
     x64_configTheory
open benchmarkLib;
open grepProgTheory;

val _ = new_theory"grep_prog_full_icompile";
val _ = Globals.max_print_depth := 10;

Definition x64_config'_def:
  x64_config' =
  let conf = x64_backend_config in
  let source_conf' = conf.source_conf with <| do_elim := F; init_vidx := 100000 |> in
  let stack_conf' = conf.stack_conf with do_rawcall := F in
    conf with <| source_conf := source_conf';
                 stack_conf := stack_conf'|>
End

val x64_conf_def = CONV_RULE (RAND_CONV EVAL) x64_config'_def; (* no optimisation *)

val x64_inc_conf = backendTheory.config_to_inc_config_def
                         |> ISPEC (x64_conf_def |> rconc)
                         |> CONV_RULE (RAND_CONV EVAL) |> rconc;


val (init_icomp_thm, init_icomp_empty, init_ic_name) = time_desc "init_icompile runtime in one file" init_icompile x64_inc_conf;

val (basis_prog_tm, grep_prog1_tm) = split_basis "grep_prog";

val (basis_prog_icomp, basis_prog_ic_name) = time_desc "icompile basis runtime in one file"
  (icompile init_ic_name init_icomp_empty "basis_prog") basis_prog_tm

val (grep_prog_icomp, grep_prog_ic_name) = time_desc "icompile grep_prog1 runtime in one file"
  (icompile basis_prog_ic_name basis_prog_icomp "grep_prog1") grep_prog1_tm;

val final_thm = time_desc "end_ic runtime in one file for grep"
  (end_icompile init_icomp_thm grep_prog_icomp grep_prog_ic_name) x64_inc_conf;

val _ = time_desc "printing the file for grep to .S file" (print_to_file final_thm) "grep_prog_full_icompiled.S"

val _ = export_theory();
