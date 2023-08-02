(*
  Compiles the hello example by evaluation inside the logic of HOL
*)
open preamble helloProgTheory compilationLib

val _ = new_theory "helloCompile"

val _ = (compilationLib.output_ILs := SOME "hello");

val hello_compiled = save_thm("hello_compiled",
  compile_x64 "hello" hello_prog_def);

(*
val backend_config_def = x64_backend_config_def;
val cbv_to_bytes = cbv_to_bytes_x64;
val name = "hello_compiled";
val prog_def = hello_prog_def;
*)

val _ = export_theory ();
