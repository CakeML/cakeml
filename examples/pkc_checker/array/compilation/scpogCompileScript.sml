(*
  Compiles the scpog example by evaluation inside the logic of HOL
*)
open preamble scpog_arrayFullProgTheory eval_cake_compile_x64Lib
open fromSexpTheory astToSexprLib

val _ = new_theory "scpogCompile"

(*
val _ = astToSexprLib.write_ast_to_file "cake_scpog.sexp" prog;
*)

Theorem scpog_array_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_scpog.S";

val _ = export_theory ();
