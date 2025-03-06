(*
  icompile grep
*)
open preamble
     eval_cake_icompile_x64Lib
     x64_configTheory
     init_icompileTheory
     basis_icompileTheory
     grepProgTheory
     benchmarkLib;

val _ = Globals.max_print_depth := 10;

val _ = new_theory"grep_prog_icompile";

fun split_basis prog_name =
  let
    val prog_const = mk_const (prog_name, “: ast$dec list”);
    val basis = EVAL “TAKE 93 ^prog_const” |> rconc;
    val prog1 = EVAL “DROP 93 ^prog_const” |> rconc;
  in
    (basis, prog1)
  end;

val (_, grep_prog1_tm) = split_basis "grep_prog";

val (grep_prog1_icomp, grep_prog1_ic_name) = time_desc "icompile grep prog1 runtime in separate file"
  (icompile "basis_prog_ic" basis_prog_icomp "grep_prog1") grep_prog1_tm

val x64_inc_conf = x64_inc_conf_def |> rconc;

val final_thm = time_desc "ending icompile for grep prog1"
  (end_icompile init_icomp_thm grep_prog1_icomp grep_prog1_ic_name) x64_inc_conf;

val _ = time_desc "printing the file for grep prog1" (print_to_file final_thm) "grep_prog1_icompiled.S";

val _ = export_theory();

