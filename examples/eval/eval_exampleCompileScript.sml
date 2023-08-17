(*
  Compiles the eval example in the logic.
*)

open preamble eval_exampleProgTheory compilationLib

val _ = new_theory"eval_exampleCompile"

Theorem eval_example_compiled =
  compile_x64 "eval_example" eval_example_prog_def

val _ = export_theory()
