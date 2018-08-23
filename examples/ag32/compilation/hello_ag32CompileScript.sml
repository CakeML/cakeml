open preamble compilationLib hello_ag32ProgTheory

val _ = new_theory "hello_ag32Compile"

val hello_compiled = save_thm("hello_compiled",
  compile_ag32 500 500 "hello" hello_prog_def);

val _ = export_theory ();
