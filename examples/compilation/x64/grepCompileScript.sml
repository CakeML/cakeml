open preamble compilationLib grepProgTheory

val _ = new_theory "grepCompile"

val grep_compiled = save_thm("grep_compiled",
  compile_x64 1000 1000 "grep" grep_prog_def);

val _ = export_theory ();
