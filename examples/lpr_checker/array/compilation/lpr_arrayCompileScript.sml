(*
  Compiles the lpr example by evaluation inside the logic of HOL
*)
Theory lpr_arrayCompile
Ancestors
  lpr_arrayFullProg
Libs
  preamble eval_cake_compile_x64Lib

(*
val _ = (OS.FileSys.mkDir "reg_alloc_x64" handle OS.SysErr _ => ());
val _ = reg_allocComputeLib.dump_to_file := SOME "reg_alloc_x64/cake_lpr_ra_";
*)

Theorem lpr_array_compiled =
  eval_cake_compile_x64 "" check_unsat_prog_def "cake_lpr.S";

(*
val _ =
  eval_cake_compile_explore_x64 "explore_"
    check_unsat_prog_def "cake_lpr_explore.txt";
*)

