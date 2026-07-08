(*
  Compiles the lpr example by evaluation inside the logic of HOL
*)
Theory lpr_arrayCompileARM8
Ancestors
  lpr_arrayFullProg
Libs
  preamble eval_cake_compile_arm8Lib

(*
val _ = (OS.FileSys.mkDir "reg_alloc_arm8" handle OS.SysErr _ => ());
val _ = reg_allocComputeLib.dump_to_file := SOME "reg_alloc_arm8/cake_lpr_ra_";
*)

Theorem lpr_array_compiled =
  eval_cake_compile_arm8 "" check_unsat_prog_def "cake_lpr_arm8.S";

