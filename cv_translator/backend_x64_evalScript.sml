(*
  Experiments with evaluating the compiler using cv_compute
*)
Theory backend_x64_eval
Libs
  preamble eval_cake_compile_x64Lib

Definition prog_def:
  prog = [] : ast$dec list
End

val res = eval_cake_compile_x64 "" prog_def "empty_prog.S";

