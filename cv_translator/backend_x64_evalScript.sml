(*
  Experiments with evaluating the compiler using cv_compute
*)
open preamble;

val _ = new_theory "backend_x64_eval";

open eval_cake_compile_x64Lib;

Definition prog_def:
  prog = [] : ast$dec list
End

val res = eval_cake_compile_x64 "" prog_def "empty_prog.S";

val _ = export_theory();
