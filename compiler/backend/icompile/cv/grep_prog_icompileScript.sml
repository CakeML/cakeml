open preamble
     eval_cake_icompile_x64Lib
     x64_configTheory
     eval_cake_compile_x64Lib
     init_icompileTheory
     basis_icompileTheory
     grepProgTheory
     benchmarkLib;

val _ = Globals.max_print_depth := 10;

val _ = new_theory"grep_prog_icompile";

val (_, grep_prog1_tm) = split_basis "grep_prog";


fun icompile_grep () = icompile "basis_prog_ic" basis_prog_icomp "grep_prog1" grep_prog1_tm;
val (grep_prog1_icomp, grep_prog1_ic_name) = time_desc "icompile grep prog1 runtime in separate file" icompile_grep();
val x64_inc_conf = x64_inc_conf_def |> rconc;
fun end_ic () = end_icompile init_icomp_thm
                             grep_prog1_icomp
                             grep_prog1_ic_name
                             x64_inc_conf;
val final_thm = time_desc "ending icompile for grep prog1" end_ic ();
fun print_the_file () = print_to_file final_thm ("grep_prog1_icompiled.S");
val _ = time_desc "printing the file for grep prog1" print_the_file ();
val _ = export_theory();
